module PTSV.Core

open System
open System.Collections
open System.Collections.Generic
open Global
open Microsoft.FSharp.Collections
open PTSV.Utils

type State = int
type LocalMemory = int
type Gamma = int

type TransOp =
    | TransState of State
    | TransTer
    | TransDiv
    | TransUp of State * LocalMemory * Gamma
    | TransDown of State * LocalMemory

let printKPTSAState q =
    match Map.tryFind q Flags.KPTSA_Q_PRINT_TABLE with
    | Some name -> name
    | None      -> $"$q{q}"
    
let printKPTSALocMem m =
    match Map.tryFind m Flags.KPTSA_M_PRINT_TABLE with
    | Some name -> name
    | None      -> $"$m{m}"
    
let printKPTSAGamma g =
    match Map.tryFind g Flags.KPTSA_G_PRINT_TABLE with
    | Some name -> name
    | None      -> $"$g{g}"

type KPTSA =
    {
        // required part
        k : int
        maxState : State
        maxLocalMemory : LocalMemory
        maxGamma : Gamma
        delta : Map<State * LocalMemory * Gamma,
                    (NumericType * TransOp) list>
        // q0 = 0; m0 = 0; gamma0 = 0 -- count new gamma from 1
        
        // for translation step count
        // mark the step count, for raw k-PTSA, no need to do this
        stepCount : Map<State * LocalMemory * Gamma * TransOp, NumericType> option
        
        // Supporting Info
        
        /// not every gamma is necessarily k, most of them may be less than k.
        /// if this information is available -- especially when translated from PAHORS, record and use this
        /// rather than pure k
        kMap : Map<Gamma, int> option
        /// state dependencies -- give one state, what is the possible state back
        /// this can be filled by translation from PAHORS, if it is originally automata, no need to fill this
        /// given a state and a gamma, if one up to this gamma with this state, what possible states will it down to
        /// because D is fixed, no need to consider if down with a specific state, what are the possible Up states.
        /// at the same time, it gives the leaving local memory
        stateDependencies : Map<State * Gamma, State list> option
    }
    /// returns the exploredSet to avoid repeat addition, accepts a hint set, if no, None should be given
    ///
    /// This function is used to detect from this configuration, whether there is a loop inside
    static member LocalEpsilonLoopDetect
        (kptsa : KPTSA) q m gamma
        (exploredSet : HashSet<State * LocalMemory * Gamma> option)
        =
        /// this set only contains those not have loops
        /// because once loop is found, one should call "Exact" directly
        let exploredSet =
            match exploredSet with
            | Some es -> es
            | None ->
                HashSet<State * LocalMemory * Gamma> ()
        /// see if from this q m gamma with the current loop trace pathSet is in a loop or not
        let rec traceLoop q m gamma pathSet =
            if Set.contains q pathSet then
                raise (MethodAccessException ())
            elif exploredSet.Contains (q, m, gamma) then ()
            else
                match Map.tryFind (q, m, gamma) kptsa.delta with
                | None -> ()
                | Some lst -> iterList q m gamma pathSet lst
                
                exploredSet.Add(q, m, gamma) |> ignore
        /// see if this q m gamma with this rule list and the current loop trace pathSet will contain any loop
        and iterList q m gamma pathSet =
            List.iter
                (fun (_, op) ->
                    match op with
                    | TransState q' -> traceLoop q' m gamma (Set.add q pathSet)
                    | _ -> ())
        let res =
            match Map.tryFind (q, m, gamma) kptsa.delta with
            | Some lst ->
                try
                    iterList q m gamma Set.empty lst
                    false
                with
                | :? MethodAccessException -> true
            | None -> false
        (res, exploredSet)
    /// return if there is any epsilon loop inside
    static member EpsilonLoopDetect (kptsa : KPTSA) =
        /// this set only contains those not have loops
        /// because once loop is found, one should call "Exact" directly
        let mutable exploredSet = HashSet<State * LocalMemory * Gamma> ()
        /// see if from this q m gamma with the current loop trace pathSet is in a loop or not
        let rec traceLoop q m gamma pathSet =
            if Set.contains q pathSet then
                raise (MethodAccessException ())
            elif exploredSet.Contains (q, m, gamma) then ()
            else
                match Map.tryFind (q, m, gamma) kptsa.delta with
                | None -> ()
                | Some lst -> iterList q m gamma pathSet lst
                
                exploredSet.Add(q, m, gamma) |> ignore
        /// see if this q m gamma with this rule list and the current loop trace pathSet will contain any loop
        and iterList q m gamma pathSet =
            List.iter
                (fun (_, op) ->
                    match op with
                    | TransState q' -> traceLoop q' m gamma (Set.add q pathSet)
                    | _ -> ())
        let iterFunc (q, m, gamma) lst =
            iterList q m gamma Set.empty lst
        try
            Map.iter iterFunc kptsa.delta
            // here means no loop happened
            false
        with
        | :? MethodAccessException -> true
        
    override x.ToString () =
        let mutable ret =
            "{\n    k = " +
                match x.kMap with
                | Some m ->
                    (Map.fold
                        (fun rs gamma k ->
                            let app = if rs = "{" then "" else "; "
                            rs + app + $"{printKPTSAGamma gamma} |-> {k}")
                        "{"
                        m) + "}"
                | None -> $"{x.k}"
                + "\n    "
        ret <- ret + $"State Amount = {x.maxState + 1}\n    Local Memory Amount = {x.maxLocalMemory + 1}\n    " +
                     $"Gamma Amount = {x.maxGamma + 1}\n    "
        
        match x.stateDependencies with
        | Some sd ->
            let s =
                Map.fold
                    (fun rs (q, gamma) lst ->
                        rs + 
                            $"{printKPTSAState q}, {printKPTSAGamma gamma} |-> " +
                            (List.fold
                                (fun rs q -> rs + (if rs = "[" then "" else ", ") + $"{printKPTSAState q}")
                                "["
                                lst) + "]\n    ")
                    ""
                    sd
            ret <- ret + "State Dependencies:\n    " + s
        | None -> ret <- ret + "No State Dependencies\n    "
        ret <- ret + "Rules:\n    "
        let s =
            Map.fold
                (fun rs (q, m, gamma) lst ->
                    let head = $"({printKPTSAState q}, {printKPTSALocMem m}, {printKPTSAGamma gamma}, "
                    rs + 
                        (List.fold
                            (fun rs (p, op) ->
                                let stepCountString =
                                    match x.stepCount with
                                    | Some sc ->
                                        match Map.tryFind (q, m, gamma, op) sc with
                                        | Some count -> $"^{count}"
                                        | None -> ""
                                    | None -> ""
                                rs + head + $"{p}, " +
                                    (match op with
                                     | TransTer -> "\\top"
                                     | TransDiv -> "\\Omega"
                                     | TransState q' -> $"{printKPTSAState q'}"
                                     | TransUp (q', m', gamma') ->
                                         $"({printKPTSAState q'}, {printKPTSALocMem m'}, " +
                                         $"Up {printKPTSAGamma gamma'})"
                                     | TransDown (q', m') ->
                                         $"({printKPTSAState q'}, {printKPTSALocMem m'}, Down)") +
                                         $"){stepCountString}\n    ")
                            ""
                            lst))
                ""
                x.delta
        ret <- ret + s + "\n}"
        ret

type VarType =
    | Varx
    | VarUp of Gamma * State
    | VarDown of State

type InteractionList =
    (State * State) list 

type Variable =
    State *
    LocalMemory *
    Gamma *
    InteractionList *
    Map<Gamma, InteractionList> *
    VarType

type RawFormula<'v> =
    | FAdd of RawFormula<'v> * RawFormula<'v>
    | FMul of RawFormula<'v> * RawFormula<'v>
    | FConst of NumericType
    | FVar of 'v
    
    override f.ToString () =
        let printFormula f = f.ToString () in
        match f with
        | FConst c -> $"{c}"
        | FAdd (e1, e2) -> $"{printFormula e1} + {printFormula e2}"
        | FMul (e1, e2) ->
            let printE e =
                match e with
                | FAdd _ -> $"({printFormula e})"
                | _ -> $"{printFormula e}"
            $"{printE e1} * {printE e2}"
        | FVar v -> $"{v}"
    
    static member (+) (f1 : RawFormula<'v>, f2 : RawFormula<'v>) =
        FAdd (f1, f2)
    static member (*) (f1 : RawFormula<'v>, f2 : RawFormula<'v>) =
        FMul (f1, f2)
    static member (-) (f1 : RawFormula<'v>, f2 : RawFormula<'v>) =
        FAdd (f1, FMul (FConst $ NUMERIC_ZERO - NUMERIC_ONE, f2))
    
    static member (*) (d : NumericType, f : RawFormula<'v>) =
        FMul (FConst d, f)
    static member (*) (f : RawFormula<'v>, d : NumericType) =
        FMul (f, FConst d)
    static member (+) (d : NumericType, f : RawFormula<'v>) =
        FAdd (FConst d, f)
    static member (+) (f : RawFormula<'v>, d : NumericType) =
        FAdd (f, FConst d)

type Formula = RawFormula<Variable>

type AnalyseResult =
    {
        /// gamma |-> the set of states that is possible to go down
        possibleDownMap : Map<Gamma, Set<State>>
        /// current gamma * target gamma |->
        ///     the set of states that is possible to go up
        possibleUpMap : Map<Gamma * Gamma, Set<State>>
        /// gamma |-> the set of states that are possible to continue evaluation
        possibleCurrentStates : Map<Gamma, Set<State>>
    }

/// some preprocessing, to acquire some information of the k-PTSA
/// including:
/// 1)  analyse possible states -- linear time complexity O(|delta|)
///     where |delta| is the size of multiset of all values, not the size of key sets
let analyseKPTSA (automata : KPTSA) : AnalyseResult =
    let mutable possibleDownMap = Map.empty
    let mutable possibleUpMap = Map.empty
    let mutable possibleCurrentStates = Map.empty
    let addNewState map key q =
        Map.add
            key
            (Set.add q
                (match Map.tryFind key map with
                | None -> Set.empty
                | Some s -> s))
            map
    Map.iter
        (fun (q, m, gamma) ->
            List.iter (fun (_, op) ->
                // when it is translated, the every up state will only be used once for a gamma
                // so the initial up state will never appear again
                if Flags.IS_TRANSLATED_KPTSA && m = 0 then ()
                else possibleCurrentStates <- addNewState possibleCurrentStates gamma q
                match op with
                | TransUp (q', _, gamma') ->
                    possibleUpMap <-
                        addNewState possibleUpMap (gamma, gamma') q'
                | TransDown (q', _) ->
                    possibleDownMap <-
                        addNewState possibleDownMap gamma q'
                | _ -> ()
            )
        )
        automata.delta
    { possibleDownMap = possibleDownMap
      possibleUpMap = possibleUpMap
      possibleCurrentStates = possibleCurrentStates
    }

let lookUpPossibleStatesList anaRes gamma gamma' pslists =
    let lookUp key map =
        match Map.tryFind key map with
        | Some l -> l
        | None -> Set.ofList []
    match Map.tryFind (gamma, gamma') pslists with
    | Some (lq, lq') -> (lq, lq', pslists)
    | None ->
        /// (q, q') of D, q means Down from gamma' and continue in gamma
        /// so it should be a possible state to Down and possible state to let gamma keep working
        /// q' means Up from gamma to gamma'
        /// so it should be a possible state to Up and possible state to let gamma' keep working
        let lq =
            Set.toList (Set.intersect
                (lookUp gamma' anaRes.possibleDownMap)
                (lookUp gamma anaRes.possibleCurrentStates))
        let lq' =
            Set.toList (Set.intersect
                (lookUp (gamma, gamma') anaRes.possibleUpMap)
                (lookUp gamma' anaRes.possibleCurrentStates))
        (lq, lq', Map.add (gamma, gamma') (lq, lq') pslists)

let createNewUp (limit : int)
    ((_, _, gamma, D, U, tp) : Variable)
    (anaRes : AnalyseResult)
    (q', m', gamma')
    (bf : Variable -> Formula)
    (_ : int)
    (pslists : Map<Gamma * Gamma, State list * State list>)
    =
    let mutable f = FConst (NumericType 0)
    let lq, lq', npsl = lookUpPossibleStatesList anaRes gamma gamma' pslists
    let passOnNewList l q =
        if Flags.IS_TRANSLATED_KPTSA then
            List.skipWhile (fun q' -> q = q') l
        else l
    let addMul u v =
        match bf u with
        | FConst c when c = NUMERIC_ZERO -> ()
        | FConst c when c = NUMERIC_ONE ->
            match bf v with
            | FConst c when c = NUMERIC_ZERO -> ()
            | vc -> f <- f + vc
        | u ->
            match bf v with
            | FConst c when c = NUMERIC_ZERO -> ()
            | v -> f <- f + (u * v)
    // Down & v
    // a dispatch process
    let rec dispatchDown lD lU tpv (* tpu is tp *) tmpq lq lq' =
        let Down = (q', 0, gamma', lD, Map.empty, tpv)
        let v = (tmpq, m', gamma, D, Map.add gamma' lU U, tp)
        addMul Down v
        if List.length lD >= limit - 1 then ()
        else
            for qn' in lq' do
                for qn in lq do
                    let nlD = (qn, qn') :: lD
                    let nlU = (qn', tmpq) :: lU
                    dispatchDown nlD nlU tpv qn (passOnNewList lq qn) (passOnNewList lq' qn')
    // execute
    for qd in lq do
        dispatchDown [] [] (VarDown qd) qd (passOnNewList lq qd) lq'
    
    
    if tp = Varx then (
        // Up & x
        let rec dispatchUp lD lU tpu tmpq lq lq' =
            if List.length lD > limit - 1 then ()
            else
                let x = (q', 0, gamma', lD, Map.empty, Varx)
                let Up = (tmpq, m', gamma, D, Map.add gamma' lU U, tpu)
                addMul x Up
                for qn' in lq' do
                    for qn in lq do
                        let nlD = (qn, qn') :: lD
                        let nlU = (qn', tmpq) :: lU
                        dispatchUp nlD nlU tpu qn (passOnNewList lq qn) (passOnNewList lq' qn')
        // execute
        for qn' in lq' do
            for qn in lq do
                dispatchUp ((qn, qn') :: []) [] (VarUp (gamma', qn')) qn (passOnNewList lq qn) (passOnNewList lq' qn')
        
        // only x
        if D = [] && Map.forall (fun _ v -> v = []) U then
            let x = (q', 0, gamma', [], Map.empty, Varx)
            match bf x with
            | FConst c when c = NUMERIC_ZERO -> ()
            | x -> f <- f + x
    )
    
    // iterate and create Down
    if limit = 0 then (FConst NUMERIC_ZERO, npsl)
    else (f, npsl)

let x0 : Variable =
    (0, 0, 0, [], Map.empty, Varx)

let rec optimiseFormula<'v> (f : RawFormula<'v>) : RawFormula<'v> =
    match f with
    | FAdd (f1, f2) ->
        match (optimiseFormula f1), (optimiseFormula f2) with
        | FConst c, f' when c = NUMERIC_ZERO -> f'
        | f', FConst c when c = NUMERIC_ZERO -> f'
        | FConst c1, FConst c2 -> FConst (c1 + c2)
        | f1', f2' -> FAdd (f1', f2')
    | FMul (f1, f2) ->
        match (optimiseFormula f1), (optimiseFormula f2) with
        | FConst c, f' when c = NUMERIC_ONE -> f'
        | f', FConst c when c = NUMERIC_ONE -> f'
        | FConst c, _ when c = NUMERIC_ZERO -> FConst NUMERIC_ZERO
        | _, FConst c when c = NUMERIC_ZERO -> FConst NUMERIC_ZERO
        | FConst c1, FConst c2 -> FConst (c1 * c2)
        | f1', f2' -> FMul (f1', f2')
    | _ -> f

type LookAheadResult =
    | LARTNone
    | LARTSome of NumericType
    | LARTOutOfBound

let printStatePairList lst =
    let s =
        List.fold
            (fun rs (q, q') -> rs + $"(q{q}, q{q'})")
            ""
            lst
    $"[{s}]"

let printPTSAVariable ((q, m, gamma, D, U, tp) : Variable) =
    let s =
        $"q{q}, m{m}, g{gamma}, "
    let sD = printStatePairList D
    let sU =
        let printGammaListPair gammaId lst =
            $"g{gammaId} : " + printStatePairList lst
        let rs =
            Map.fold
                (fun rs gammaId lst ->
                    match rs with
                    | None -> Some (printGammaListPair gammaId lst)
                    | Some s -> Some (s + ", " + printGammaListPair gammaId lst))
                None
                U
        let s =
            match rs with
            | None -> ""
            | Some s -> s
        $"{{{s}}}"
    let s = s + sD + ", " + sU
    match tp with
    | Varx -> $"x{{{s}}}"
    | VarDown qd ->
        $"Down{{{s}, q{qd}}}"
    | VarUp (gUp, qUp) ->
        $"Up{{{s}, (q{qUp}, g{gUp}}}"

let rec printFormula f =
    match f with
    | FConst c -> $"{c}"
    | FAdd (e1, e2) -> $"{printFormula e1} + {printFormula e2}"
    | FMul (e1, e2) ->
        let printE e =
            match e with
            | FAdd _ -> $"({printFormula e})"
            | _ -> $"{printFormula e}"
        $"{printE e1} * {printE e2}"
    | FVar v -> printPTSAVariable v

/// construct the function \scriptF from a k-PTSA
/// only construct those relevant to the final result
/// return a list of variables and its corresponding formula
///
/// Old slow algorithm, use constructNewPrimitiveEquationSystem instead
let constructPrimitiveEquationSystem_Old
    (automata : KPTSA) : (Variable * Formula) list =
    let analyseResult = analyseKPTSA automata
    let mutable possibleStatesLists = Map.empty
    let mutable ret = []
    /// those already met for the first time, which means they will be tackled
    let mutable already =
        let table = Hashtable ()
        table.Add(x0, None)
        table
    let todo = Queue<Variable> ()
    let mutable lookForwardCount = 0
    let mutable exploredCount : uint64 = uint64 0  // it seems that use already.Count is heavy
    let lookUp key map =
        match Map.tryFind key map with
        | Some l -> l
        | None -> []
    let addToAlready v (c : NumericType option) =
        if already.ContainsKey v then
            already.[v] <- c
        else
            match c with
            | Some c ->
                if Flags.TEST_PRINT_CONST_VAR then
                    printfn $"{printPTSAVariable v} is: {c}."
            | None -> ()
            already.Add(v, c)
    let tryFindNumericTypeHashtable v (table : Hashtable) =
        if table.ContainsKey v then
            Some (already.[v] :?> NumericType option)
        else None
    let tryFindAlready v = tryFindNumericTypeHashtable v already
    let addNewExplored v c =
        addToAlready v c
        exploredCount <- exploredCount + uint64 1
        if Flags.DEBUG then
            Console.Write $"\rCurrent Explored Variables: {exploredCount}"
        if exploredCount > Flags.MAXIMUM_ALLOWED_VARIABLE_AMOUNT then
            failwith $"Too many variables, its over {Flags.MAXIMUM_ALLOWED_VARIABLE_AMOUNT}."
        if Flags.DEBUG && (exploredCount % uint64 10000 = uint64 0) then
            // empty to replace the string after this
            printfn $"\rExplored {exploredCount} variables.               "
    /// if exists, see if it is a cached constant:
    ///     if then, return a const with cached value
    ///     if not, wrap a variable wrap with v
    /// if not exists, add to todoList, return a variable wrap with v, cache nothing
    let addTodo lookAhead v =
        match tryFindAlready v with
        | Some (Some c) -> FConst c
        | Some None -> FVar v
        | None ->
            match lookAhead v with
            | LARTSome c ->
                lookForwardCount <- lookForwardCount + 1
                addNewExplored v (Some c)
                FConst c
            | LARTNone ->
                // this is because when lookAhead v, this variable itself may appear, and have already been added
                // to the todoList
                match tryFindAlready v with
                | Some None -> ()
                | None ->
                    addNewExplored v None
                    todo.Enqueue v
                | _ ->
                    // this is impossible, because when it is already added, it means it has a loop dependence
                    // which means its RHS has at least itself and thus not a constant
                    failwith "Impossible."
                FVar v
            | LARTOutOfBound -> FVar v
    /// just to see if this has constant value
    /// count represents, at most, how many levels of variables for a time to look
    let rec simpleLookAhead count v =
        if count <= 0 then
            match tryFindAlready v with
            | Some (Some c) -> LARTSome c
            | _ ->
                // if the maximum look ahead number is 0, this means do not look ahead, so just enqueue this
                // for if we return OutOfBound as usual for the last element, this element will not be enqueued.
                //
                // note that this is not an elegant way of solving this, may be we should distinguish the root
                // look ahead by another function.
                if Flags.LOOK_AHEAD_NUM <= 0 then LARTNone
                else LARTOutOfBound
        else
            // this one is slower because the comparison itself will take more time.
//            let newLookAhead v' =
//                /// if the new variable is the same with the current, it must going to get out of bound
//                if v = v' then LARTOutOfBound
//                else simpleLookAhead (count - 1) v'
//            let f = consOne v (addTodo newLookAhead)
            let f = consOne v (addTodo (simpleLookAhead (count - 1)))
            match f with
            | FConst c -> LARTSome c
            | _ -> LARTNone
    /// construct one element of the final result, returns the formula constructed for the variable
    /// everytime a variable is generated from this place, call the addTodo function to tackle the encountered variable
    and consOne (v : Variable) (addTodo : Variable -> Formula) =
        checkTimeOut ()
        let q, m, gamma, D, U, tp = v
        let mutable f = FConst NUMERIC_ZERO
        let noMission = (D = []) && (Map.forall (fun _ (vl : InteractionList) -> vl.Length = 0) U)
        for p, op in lookUp (q, m, gamma) automata.delta do
            // generate a formula for this variable v
            let np = (
                match op with
                | TransTer ->
                    if noMission && tp = Varx then FConst NUMERIC_ONE
                    else FConst NUMERIC_ZERO
                | TransDiv -> FConst NUMERIC_ZERO
                | TransState q' ->
                    let v' = (q', m, gamma, D, U, tp)
                    addTodo v'
                | TransUp (q', m', gamma') ->
                    match U.TryFind gamma' with
                    // gamma' in dom(U)
                    | Some ((qn, qn') :: lU) ->
                        if q' = qn then
                            let v' = (qn', m', gamma, D, Map.add gamma' lU U, tp)
                            addTodo v'
                        else FConst NUMERIC_ZERO
                    // gamma' for Up
                    | Some [] ->
                        if noMission && tp = VarUp (gamma', q') then FConst NUMERIC_ONE
                        else FConst NUMERIC_ZERO
                    // gamma' notin dom(U)
                    | None ->
                        let nf, npsl =
                            createNewUp
                                (match automata.kMap with
                                 | None -> automata.k
                                 // the plan of going up to gamma', not the current gamma
                                 | Some map -> Map.find gamma' map)
                                v analyseResult
                                (q', m', gamma')
                                addTodo
                                automata.maxState
                                possibleStatesLists
                        possibleStatesLists <- npsl
                        nf
                | TransDown (q', m') ->
                    match D with
                    | [] ->
                        if noMission && tp = VarDown q' then
                            FConst NUMERIC_ONE
                        else FConst NUMERIC_ZERO
                    | (qn, qn') :: lD ->
                        if q' = qn then
                            let v = (qn', m', gamma, lD, U, tp)
                            addTodo v
                        else FConst NUMERIC_ZERO
            )
            f <- f + p * np
        optimiseFormula f
    
    /// a simple shortcut function
    let constructFormula v = consOne v (addTodo (simpleLookAhead Flags.LOOK_AHEAD_NUM))
    ret <- [(x0, constructFormula x0)]
    let addToRet v f =
        ret <- (v, f) :: ret
    while todo.Count > 0 do
        let v = todo.Dequeue()
        let f = constructFormula v
        let cacheConst c = addToAlready v (Some c)
        match f with
        | FConst c when c = NUMERIC_ZERO -> cacheConst NUMERIC_ZERO
        | FConst c ->
            cacheConst c
            addToRet v f
        | _ -> addToRet v f
    
    let totalVariableExplored = already.Count
    
    let erasedCount =
        let mutable counter = 0
        for k in already do
            let k = k :?> DictionaryEntry
            if k.Value :?> NumericType option <> None then
                counter <- counter + 1
        counter
    
    // finally, substitute all those been cached
    // no need to erase anything, because it is not the case
//    let eraseMap =
//        Map.map
//            (fun _ v ->
//                match v with
//                | Some c -> c
//                | None -> failwith "Impossible")
//            (Map.filter (fun _ v -> v <> None) already)
    
    if not Flags.INNER_DEBUG && Flags.DEBUG then
        printfn $"\nTotal variables explored: {totalVariableExplored}"
        printfn $"Erased Variables: {erasedCount}"
    
    if Flags.INNER_DEBUG then
        printfn $"\nTotal variables explored: {totalVariableExplored}"
        printfn $"Redundant variables during primitive formula construction: {erasedCount}"
        printfn $"Look forward count: {lookForwardCount}"
    
    let rec substituteVar e =
        match e with
        | FVar v ->
            match tryFindAlready v with
            | Some (Some v) -> FConst v
            | Some None -> e
            | None -> e
        | FAdd (e1, e2) -> FAdd (substituteVar e1, substituteVar e2)
        | FMul (e1, e2) -> FMul (substituteVar e1, substituteVar e2)
        | FConst _ -> e
    
    // filter out const e when it is not x0
    // this is because some constant variables are added to the todoList due to the end of look ahead
    // that is, when the variable appears, the counter of look ahead is 1, which means it has no chance to further see
    // if its related variable is constant, it is also constant.
    //
    // this is right:
    // because the erase map will contain all possible constants, so the constants do not need to be recorded again here
    let rec filterAndMap lst =
        match lst with
        | (i, e) :: lst' ->
            if (match e with
                | FConst _ -> true
                | _ -> false) && i <> x0 then filterAndMap lst'
            else
                (i, substituteVar e) :: (filterAndMap lst')
        | [] -> []
    
    ret <- filterAndMap ret
    
    ret

type NewVariableType =
    | NVTTer
    | NVTTrips
    | NVTProbTrips  // this is just for special mark, do not use it in other places

/// the new representation of variables
/// the parity of state list should show the type, but we add type notation for simplicity
type NewVariable = State list * Gamma * NewVariableType

let x0New : NewVariable = ([0], 0, NVTTer)

type NewFormula = RawFormula<NewVariable>

let printNewFormulaVariable (v : NewVariable) =
    let D, gamma, tp = v
    let sD =
        (List.fold
            (fun s q ->
                let f = if s = "[" then "" else ", "
                s + f + $"q{q}")
            "["
            D) + "]"
    let s =
        $"(g{gamma}){{{sD}}}"
    match tp with
    | NVTTer -> "Ter" + s
    | NVTTrips -> "Trips" + s
    | NVTProbTrips -> $"P[Trips{s}]"
    
let rec printNewFormula (f : NewFormula) =
    let recall = printNewFormula
    let recallWithJudge f =
        match f with
        | FAdd _ -> "(" + recall f + ")"
        | _ -> recall f
    match f with
    | FAdd (f1, f2) ->
        recall f1 + " + " + recall f2
    | FMul (f1, f2) ->
        recallWithJudge f1 + " * " + recallWithJudge f2
    | FConst c -> $"{c}"
    | FVar v -> printNewFormulaVariable v
    
let printNewFormulaSystem l =
    List.fold
        (fun r (v, f) ->
            r + printNewFormulaVariable v + " = " + printNewFormula f + "\n")
        ""
        l

/// add the new q that goes all the way down to gamma0 to terminate
/// it is safe to stateDependencies, because the new qQuit will not have any dependencies and it will not
/// change the other's dependencies
///
/// Also modify KPTSA rule
///
/// Note that for new algorithm, this change may slower the process, as it add new state dependencies
let normaliseKPTSA (kptsa : KPTSA) =
    let qQuit = kptsa.maxState + 1
    let qDiv = qQuit + 1
    let mQuit = kptsa.maxLocalMemory + 1
    let mutable stepCount =
        match kptsa.stepCount with
        | Some sc -> sc
        | None -> Map.empty
    // algorithm framework:
    //      change all tt to down rule -- for epsilon elimination, not including gamma0
    //      add tt rule to this new state for gamma0
    //      relevant stateDependencies add this new state -- this may slower the process
    /// the new rule set and gammas who contain tt in it
    let rules, hasTerGammas, hasDivGammas =
        let foldFunc (rm, hasTerGammas : HashSet<Gamma>, hasDivGammas : HashSet<Gamma>) (q, m, gamma) lst =
            if gamma = 0 then
                Map.add (q, m, gamma) lst rm, hasTerGammas, hasDivGammas
            else
                Map.add
                    (q, m, gamma)
                    (List.map
                        (fun (p, op) ->
                            match op with
                            | TransTer ->
                                match Map.tryFind (q, m, gamma, op) stepCount with
                                | Some count ->
                                    stepCount <-
                                        Map.add (q, m, gamma, TransDown (qQuit, mQuit)) count
                                            (Map.remove (q, m, gamma, op) stepCount)
                                | None -> ()
                                hasTerGammas.Add gamma |> ignore
                                (p, TransDown (qQuit, mQuit))
                            | TransDiv ->
                                hasDivGammas.Add gamma |> ignore
                                (p, TransDown (qDiv, mQuit))
                            | _ -> (p, op))
                        lst)
                    rm,
                hasTerGammas, hasDivGammas
        Map.fold foldFunc (Map.empty, HashSet<Gamma> (), HashSet<Gamma> ()) kptsa.delta
    
    let mutable rules =
        Map.map
            (fun _ -> List.filter (fun (p, _) -> p > NUMERIC_ZERO))
            rules
    
    // those already added
    let visitedLMGammas = HashSet<LocalMemory * Gamma> ()
    // possible Up q', _, gamma' map
    let upMap = HashSet<State * Gamma * TransOp> ()
    
    // should add things into hasTerGammas, hasDivGammas
    let mutable changed = true
    while changed do
        changed <- false
        let mutable newRules = rules
        let iterFunc (_, _, gamma) lst =
            let iterFunc (_, op) =
                match op with
                | TransUp (q', m', gamma') ->
                    let toTer = hasTerGammas.Contains gamma'
                    let toDiv = hasDivGammas.Contains gamma'
                    if toTer then
                        upMap.Add (q', gamma', TransTer) |> ignore
                    if toDiv then
                        upMap.Add (q', gamma', TransDiv) |> ignore
                    if toTer || toDiv then
                        if visitedLMGammas.Add (m', gamma) then
                            let addToNewRuleAndStepCount qType opType =
                                newRules <-
                                    Map.add
                                        (qType, m', gamma)
                                        (if gamma = 0 then
                                             [NUMERIC_ONE, opType]
                                         else
                                             [NUMERIC_ONE, TransDown (qType, mQuit)])
                                        newRules
                                // bugfix : final termination should not have count
//                                if gamma = 0 && kptsa.stepCount <> None then
//                                    stepCount <- Map.add (qType, m', 0, opType) NUMERIC_ONE stepCount
                            
                            if toTer then
                                addToNewRuleAndStepCount qQuit TransTer
                                if gamma <> 0 then
                                    hasTerGammas.Add gamma |> ignore
                            if toDiv then
                                addToNewRuleAndStepCount qDiv TransDiv
                                if gamma <> 0 then
                                    hasDivGammas.Add gamma |> ignore
                            
                            changed <-
                                if gamma = 0 then changed
                                else true
                | _ -> ()
            List.iter iterFunc lst
        Map.iter iterFunc rules
        rules <- newRules
    
    // find only relevant gamma_s -- the one that will go into those with qQuit to add down rules
    let stateDependencies =
        match kptsa.stateDependencies with
        | Some sd ->
            let mutable m =
                Map.map
                    (fun (q, gamma) lst ->
                        upMap.Remove (q, gamma, TransTer) |> ignore
                        upMap.Remove (q, gamma, TransDiv) |> ignore
                        let lst =
                            if hasTerGammas.Contains gamma then
                                qQuit :: lst
                            else lst
                        let lst =
                            if hasDivGammas.Contains gamma then
                                qDiv :: lst
                            else lst
                        lst)
                    sd
            for q, gamma, op in upMap do
                m <-
                    let qType =
                        match op with
                        | TransDiv -> qDiv
                        | TransTer -> qQuit
                        | _ -> failwith "Not a valid Op Type Here."
                    let lst =
                        match Map.tryFind (q, gamma) m with
                        | Some lst -> qType :: lst
                        | None -> [qType]
                    Map.add (q, gamma) lst m
            Some m
        | None -> None
    
    let stepCount =
        match kptsa.stepCount with
        | Some _ -> Some stepCount
        | None -> None
    
    let ret =
        {
            kptsa with
                maxState = qQuit
                maxLocalMemory = mQuit
                delta = rules
                stateDependencies = stateDependencies
                stepCount = stepCount
        }
    
    innerDebugPrint $ "Normalised rPTSA.\n" + $"{ret}"
    
    ret

exception NFMarkException of NewVariable

/// the framework function of constructing values of termination probability and expected termination time
/// a key point to note: we assume no loops (pure `TransState` loop) in the rules of the given k-PTSA
/// if not sure, please call epsilonElimination_Exact first for definite loop elimination
let Framework_constructNewPrimitiveFormulaSystem
    // () -> initial variable return information
    initVarRetAccVal
    // config acc info -> current variable returning info -> fold result of upMap -> the new variable return information
    updateVarRetAccVal
    // current variable return information -> the implied return formula
    genRetFormulaFromVarRetAccVal
    // () -> initial config accumulative info
    initConfigAccInfo
    // probability of current rule -> previous config accumulative info -> new (current) config accumulative info
    updateConfigAccInfo
    // current config accumulative info -> ?Target Termination Point? -> initial folding element
    foldInitVal
    // current config accumulative info -> current fold res -> computed variable info -> next accumulating fold result
    foldRetFunc
    // whether the return value should also contain constant (non-0) values
    (alsoConstantValues : bool)
    (normalise : bool)
    (kptsa : KPTSA)
    : (NewVariable * NewFormula) list =
    // bugfix : the generated stateDependencies is done
//    let kptsa = {
//        kptsa with stateDependencies = None
//    }
    let kptsa =
        if normalise then
            normaliseKPTSA kptsa
        else
            kptsa
    /// the variables already explored
    /// type should be: Map<NewVariable, NumericType option>
    let already = Hashtable ()
    let mutable varCount : uint64 = uint64 0
    // use these function rather than use "already" directly
    let lookUpAlready key =
        if already.ContainsKey key then
            Some (already.[key] :?> NumericType option)
        else None
    let addAlready v (c : NumericType option) =
        // this definition should be faster as in most of the cases, just add a new entry
        try
            already.Add(v, c)
            varCount <- varCount + uint64 1
            if Flags.DEBUG then
                Console.Write $"\rExplored Variables: {varCount}"
        with
        | :? ArgumentException -> already.[v] <- c
    let mutable ret = []
    /// gammaDownStates: given a gamma to Up, what is the possible Down states from this gamma
    /// lmGammaPossibleStates: given the current m and gamma, what is the possible q to continue working
    /// no need to compute when there is actually a stateDependencies map attached to the given automata
    let gammaDownStates, lmGammaPossibleStates =
        match kptsa.stateDependencies with
        | Some _ -> Map.empty, Map.empty
        | None ->
            let addToSetMap k v map =
                match Map.tryFind k map with
                | Some s -> Map.add k (Set.add v s) map
                | None -> Map.add k (Set.add v Set.empty) map
            Map.fold
                (fun (ds, ps) (q, m, gamma) lst ->
                    let nds =
                        List.fold
                            (fun ds (_, op) ->
                                match op with
                                | TransDown (q', _) -> addToSetMap gamma q' ds
                                | _ -> ds)
                            ds
                            lst
                    (nds, addToSetMap (m, gamma) q ps))
                (Map.empty, Map.empty)
                kptsa.delta
    // given the "current local memory" and "local gamma" and the "target gamma", what is the possible down state list
    let mutable quasi_StateDependencies : Map<LocalMemory * Gamma * Gamma, State list> = Map.empty
    let zeroTrips = HashSet<Gamma * State list> ()
    let zeroTers = HashSet<Gamma * State list> ()
    /// the function to construct formula for the given variable
    /// if it is cached in already, return the value right away
    /// if it is within the pathSet, return value right away
    /// if it is not in the pathSet and also not a constant, record itself to return list
    /// returns if it is constant
    let rec consVar v pathSet : NumericType option =
        checkTimeOut ()
        let D, gamma, tp = v
        /// construct the formula without examining any cache information
        /// this is called when all information check is done
        let rec consFormula () =
            let q, D =
                match D with
                | q :: D -> q, D
                | [] -> failwith "Invalid variable"
//            /// the return value, everytime valid UpMap is computed, add to this variable
//            let mutable retF = FConst NUMERIC_ZERO
            let mutable varRetAccValue = initVarRetAccVal ()
            /// the updated pathSet, includes the current v
            let pathSet = Set.add v pathSet
            let rec computeConfig
                (q, m, gamma)
                configAccInfo
                D
                (upMap : Map<Gamma, State list>) : unit =
                checkTimeOut ()
                /// start to compute if all upMap is possible, if it is, add this to pathSet
                /// if it is not -- if any of them is 0, throw exception
                /// the parameter is what to get to terminate, if None, then all are regarded as Trips
                /// give the gamma and the new D for this gamma -- as upMap only has even-length stuff
                let computeUpMap configAccInfo terGamma =
                    let computeNV (nv : NewVariable) =
                        match consVar nv pathSet with
                        | Some c when c = NUMERIC_ZERO ->
                            // if this is impossible, raise the exception right away until the source of this nv
                            raise (NFMarkException nv)
                        | Some c -> FConst c
                        | None -> FVar nv
                    let foldFunc r gamma D =
                        let nv = (D, gamma, NVTTrips)
//                        f * (computeNV nv)
                        foldRetFunc configAccInfo r (computeNV, nv)
                    let initConfig, foldFunc =
                        match terGamma with
                        | Some (tg, tD) ->
                            let nv = (tD, tg, NVTTer)
//                            prob * (computeNV nv),
                            foldInitVal configAccInfo (Some (computeNV, nv)),
                            (fun r gamma sList -> if gamma = tg then r else foldFunc r gamma sList)
                        | None ->
//                            FConst prob, foldFunc
                            foldInitVal configAccInfo None, foldFunc
                    varRetAccValue <-
                        updateVarRetAccVal configAccInfo varRetAccValue (Map.fold foldFunc initConfig upMap)
                
                let iterFunc (p, op) =
                    let newConfigAccInfo =
                        updateConfigAccInfo kptsa (q, m, gamma, p, op) configAccInfo
                    match op with
                    | TransTer ->
                        // if it is to termination, then if D is also empty, start distributing
                        match tp with
                        | NVTTer ->
                            if List.isEmpty D then
                                computeUpMap newConfigAccInfo None
                            else ()
                        | NVTTrips -> ()
                        | NVTProbTrips -> failwith "INTERNAL: This kind of variable should not be evaluated."
                    | TransDiv -> ()
                    | TransState q' -> computeConfig (q', m, gamma) newConfigAccInfo D upMap
                    | TransDown (q', m') ->
                        // go according to D
                        match D with
                        | qn :: qn' :: D' when qn = q' ->
                            // should continue with D'
                            computeConfig (qn', m', gamma) newConfigAccInfo D' upMap
                        | [qn] when qn = q' ->
                            if tp <> NVTTrips then
                                failwith "Invalid Variable, a Ter type with even length D."
                            // it means it has finished all its computation, so just start distributing
                            computeUpMap newConfigAccInfo None
                        | _ -> ()
                    | TransUp (q', m', gamma') ->
                        let gamma'D =
                            match Map.tryFind gamma' upMap with
                            | Some lst -> List.append lst [q']
                            | None -> [q']
                        if tp = NVTTer &&
                           (not normalise) &&
                           List.isEmpty D && not (zeroTers.Contains (gamma', gamma'D)) then
                            // this means we are OK to distribute, try not coming down
                            try
                                computeUpMap newConfigAccInfo (Some (gamma', gamma'D))
                            with
                            | NFMarkException nv when nv = (gamma'D, gamma', NVTTer) ->
                                // this means to stop going up finding the source
                                zeroTers.Add(gamma', gamma'D) |> ignore
                        // even if it cannot terminate with this new gamma'D, it is still possible to get Down
                        // for an example, if the termination point can only be root, any up ter is 0 but still possible
                        //    for longer list to get Down.
                        // continue computation
                        let possibleDownStates =
                            match kptsa.stateDependencies with
                            | Some sd ->
                                match Map.tryFind (q', gamma') sd with
                                | Some lst -> lst
                                | None -> []
                            | None ->
                                match Map.tryFind (m', gamma, gamma') quasi_StateDependencies with
                                | Some lst -> lst
                                | None ->
                                    match Map.tryFind gamma' gammaDownStates,
                                          Map.tryFind (m', gamma) lmGammaPossibleStates with
                                    | Some s1, Some s2 ->
                                        let ret = Set.toList (Set.intersect s1 s2)
                                        quasi_StateDependencies <-
                                            Map.add (m', gamma, gamma') ret quasi_StateDependencies
                                        ret
                                    | _, _ ->
                                        quasi_StateDependencies <-
                                            Map.add (m', gamma, gamma') [] quasi_StateDependencies
                                        []
                        // bugfix : the same nq with different lm
                        for nq in possibleDownStates do
                            let gamma'D = List.append gamma'D [nq]
                            let k =
                                match kptsa.kMap with
                                | None -> kptsa.k
                                | Some m ->
                                    match Map.tryFind gamma' m with
                                    | None -> kptsa.k
                                    | Some k -> k
                            // if this trips is shown to be 0, any trips longer than that must be 0 too.
                            // this can be seen by that longer trips must go through shorter trips experience
                            // while 0 means the shorter trip will get stuck, so the same to the longer one
                            if List.length gamma'D / 2 <= k && not (zeroTrips.Contains (gamma', gamma'D)) then
                                let newUpMap = Map.add gamma' gamma'D upMap
                                try
                                    computeConfig (nq, m', gamma) newConfigAccInfo D newUpMap
                                with
                                | NFMarkException nv when nv = (gamma'D, gamma', NVTTrips) ->
                                    zeroTrips.Add(gamma', gamma'D) |> ignore
                match Map.tryFind (q, m, gamma) kptsa.delta with
                | Some lst -> List.iter iterFunc lst
                | None -> ()
            // the first computation will not raise any marked exception
            computeConfig (q, 0, gamma) (initConfigAccInfo ()) D Map.empty
            genRetFormulaFromVarRetAccVal varRetAccValue
        
        if Set.contains v pathSet then
            addAlready v None
            None
        else
            match lookUpAlready v with
            | Some c ->
                // the lines for making all meaningful parts explicit
//                match c with
//                | Some zero when zero = NUMERIC_ZERO -> c
//                | _ -> None
                c
            | None ->
                if List.length D / 2 > kptsa.k then
                    // no need to cache
                    Some NUMERIC_ZERO
                else
                    let f = consFormula ()
                    match f with
                    | FConst c ->
                        addAlready v (Some c)
                        // the lines for making all meaningful parts explicit
//                        if c = NUMERIC_ZERO then Some NUMERIC_ZERO
//                        else None
                        (Some c)
                    | _ ->
                        addAlready v None
                        ret <- (v, f) :: ret
                        None
    
    match consVar x0New Set.empty with
    | Some c ->
        // if it is const, follow the convention of consVar, it should not be added to ret
        // as we only care about the value of x0, we are safe to just add this variable to ret
        // on the other hand, one may be able to show that if x0 is const, ret itself will be empty
        // as once there is something in ret, it means from x0, there is some variable not const
        // so x0 will not be const too.
        ret <- [x0New, FConst c]
    | None -> ()
    
    printfn ""  // so to end the variable count.
    printfn $"Totally explored {varCount} variables."
    
    if alsoConstantValues then
        for e in already do
            let e = e :?> DictionaryEntry
            match e.Value :?> NumericType option with
            | Some c ->
                let nv = e.Key :?> NewVariable
                // because x0New has been added separately, so here even if it is constant, should not be added again
                if c <> NUMERIC_ZERO && nv <> x0New then
                    let c =
                        if c = Const.NUMERIC_MARK_NUMBER then NUMERIC_ZERO
                        else c
                    ret <- (nv, FConst c) :: ret
            | _ -> ()
    
    if Flags.INNER_DEBUG then
        printfn "============================ Zero Value Variables ============================"
        let mutable counter = 0
        for e in already do
            let e = e :?> DictionaryEntry
            match e.Value :?> NumericType option with
            | Some c ->
                let v = e.Key :?> NewVariable
                if c = NUMERIC_ZERO then
                    Console.Write $"{printNewFormulaVariable v}  "
                    counter <- counter + 1
                    if counter % 4 = 0 then
                        printfn ""
            | None -> ()
        printfn "\n========================== End Zero Value Variables =========================="
        printfn "\n========================== Other Constant Variables =========================="
        
        for e in already do
            let e = e :?> DictionaryEntry
            match e.Value :?> NumericType option with
            | Some c ->
                let v = e.Key :?> NewVariable
                if c <> NUMERIC_ZERO then
                    printfn $"{printNewFormulaVariable v} = {c}"
            | None -> ()
        
        printfn "\n======================== End Other Constant Variables ========================"
    
    let rec substituteFormulaVar f =
        match f with
        | FVar (v as (D, g, nvt)) ->
            let v =
                match nvt with
                | NVTProbTrips -> (D, g, NVTTrips)
                | _            -> v in
            match lookUpAlready v with
            | Some None -> f
            | Some (Some c) -> FConst c
            | None -> IMPOSSIBLE ()
        | FAdd (f1, f2) -> FAdd (substituteFormulaVar f1, substituteFormulaVar f2)
        | FMul (f1, f2) -> FMul (substituteFormulaVar f1, substituteFormulaVar f2)
        | FConst _ -> f
    ret <- List.map (BiMap.sndMap substituteFormulaVar) ret 
    
    ret
    
/// just a very simple function to remove all head zeros and ones
/// as a simplified version of optimiseFormula
let rec quickZeroOneRemoval f =
    match f with
    | FAdd (FConst c, f') when c = NUMERIC_ZERO -> quickZeroOneRemoval f'
    | FAdd (f1, f2) -> FAdd (quickZeroOneRemoval f1, quickZeroOneRemoval f2)
    | FMul (FConst c, f') when c = NUMERIC_ONE -> quickZeroOneRemoval f'
    | FMul (f1, f2) -> FMul (quickZeroOneRemoval f1, quickZeroOneRemoval f2)
    | _ -> f
    
    
/// the function of constructing termination probability value primitive formula system
/// this system will not be linear, and should be solved by other method
let constructNewPrimitiveFormulaSystem returnConstants normalise =
    Framework_constructNewPrimitiveFormulaSystem
        (fun () -> FConst NUMERIC_ZERO)
        (fun _ f foldRes -> f + (optimiseFormula foldRes))
        optimiseFormula
        // the initial accumulative probability is just 1
        (fun () -> NUMERIC_ONE)
        (fun _ (_, _, _, p, _) prob -> p * prob)
        (fun prob v ->
            match v with
            | None -> FConst prob
            | Some (f, v) -> prob * f v)
        (fun _ formula (f, v) -> formula * f v)
        returnConstants
        normalise

/// the function of constructing primitive formula system for expected termination time
/// the resulting system is a linear one, and thus is able to be solved by Gaussian Elimination
/// This function should only be used when the model is guaranteed to be AST
/// 
/// Implementation Notes:
///     must pay attention that the Gaussian Elimination process is not guaranteed to compute a good value
///     as in the epsilon elimination, we must treat it as normal Gaussian Elimination, there will be cases where the
///     value may be infinity.
///
/// para: Return Standard Form means to not replacing constant values in Expected Termination Probability
///
/// returns two parts: the first is probability part and then the expected termination time computation part
/// solution can be found by: first iterating the first one, replace the variable values, then apply to Gaussian Elimination
let constructPrimitiveExpectedTerminationTimeFormulaSystem retStandardForm kptsa =
    let changeToProbTrips (gamma, D, tp) =
        match tp with
        | NVTTrips -> (gamma, D, NVTProbTrips)
        | NVTTer -> failwith "INTERNAL: changing Ter to ProbTrips."
        | NVTProbTrips -> failwith "INTERNAL: re-changing ProbTrips to ProbTrips."
    let rec changeFormulaToProTrips f =
        let recall = changeFormulaToProTrips
        match f with
        | FAdd (f1, f2) -> FAdd (recall f1, recall f2)
        | FMul (f1, f2) -> FMul (recall f1, recall f2)
        | FConst _ -> f
        | FVar v -> FVar (changeToProbTrips v)
    /// the probability part for the return value
    let (probPart : (NewVariable * NewFormula) list,
        // Hashtable : new-variable |-> NumericType option, if it is constant, return Some val, or, None.
         consMap) =
        // note that all constant results will not be contained within non-constants, they're all replaced
        let res = constructNewPrimitiveFormulaSystem true true kptsa
        List.fold
            (fun (probPart, consMap : Hashtable) (nv, f) ->
                // filter out x0New, for this may conflict with the E(Ter)
                if nv = x0New then (probPart, consMap)
                else
                    match f with
                    // no need to treat x0 specially, because P(x0) will not affect anything
                    | FConst c ->
                        consMap.Add(nv, Some c)
                        if retStandardForm then
                            ((changeToProbTrips nv, changeFormulaToProTrips f) :: probPart, consMap)
                        else
                            (probPart, consMap)
                    | _ ->
                        consMap.Add(nv, None)
                        ((changeToProbTrips nv, changeFormulaToProTrips f) :: probPart, consMap))
            ([], Hashtable ())
            res
    let foldConsNvValue (varSet, consParts : Hashtable) (computeNv, nv) =
        match computeNv nv with
        | FVar _ -> ()
        | FConst c -> consParts.Add(nv, c)
        | _ -> failwith "Impossible"
        Set.add nv varSet, consParts
    if Flags.INNER_DEBUG then
        // just a self-containing hint on information to print
        printfn "In following equation system, variable has value -1 means it has length count 0 but there is a path."
        printfn "Distinguished from zero value variables, which are variables that no path exists."
    (probPart,
        Framework_constructNewPrimitiveFormulaSystem
            // this table should be:
            //      a var set to (constant variable map, current mean value, current total probability value)
            // this should be a function as if we just create one, this one will be modified for multiple variables
            Hashtable
            // bugfix : varSet should contain all variables rather than just non-constants
            // the fold function should return: varSet, constant variable map -- constant variables to NumericType
            // Note that we cannot use Hashset as it does not has hashcode that reflects its structure, but Set has
            (fun (steps : NumericType, pathProb) table (varSet : Set<NewVariable>, consVars : Hashtable) ->
                let tabVal = table.[varSet]
                if tabVal <> null then
                    let consPart, curMean, curWeight = tabVal :?> Hashtable * NumericType * NumericType
                    // adopt a light comparison, not complete
                    // also note that Hashtable like HashSet, does not have structural comparison or structural hash
                    if consVars.Count <> consPart.Count then
                        failwith "Two constant var set not the same."
                    let newConsPart = consPart  // unchanged, for the constant variables should be the same
                    let newWeight = curWeight + pathProb
                    let newMean = (curMean * curWeight + (steps * pathProb)) / newWeight
                    table.[varSet] <- (newConsPart, newMean, newWeight)
                else
                    table.Add(varSet, (consVars, steps, pathProb))
                table)
            // turn var acc ret val into a formula
            (fun table ->  // Set<NewVariable> -> (NewVariable -> NumericType) * NumericType * NumericType
                /// generate probability product for given varSet, except the given variable
                let genProbProd takeOutConst varSet exceptV =
                    (if takeOutConst then
                        optimiseFormula
                     else quickZeroOneRemoval)
                        (Set.fold
                            (fun nf nv ->
                                if exceptV = Some nv then nf
                                elif takeOutConst then
                                    match consMap.[nv] :?> NumericType option with
                                    | Some c -> nf * c
                                    | None -> nf * FVar (changeToProbTrips nv)
                                else
                                    nf * FVar (changeToProbTrips nv))
                            (FConst NUMERIC_ONE)
                            varSet)
                let retAddTag optimisedF =
                    match optimisedF with
                    | FConst c when c = NUMERIC_ZERO ->
                        FConst Const.NUMERIC_MARK_NUMBER
                    | _ -> optimisedF
                // notAbug : table is 0 does not necessarily mean nothing -- U may be empty
                // but this is captured by an Empty varSet, if this Count <= 0, it means impossible
                if table.Count <= 0 then FConst NUMERIC_ZERO
                elif retStandardForm then
                    // target: (totally standard form)
                    //      \sum_U ((\sum_i v_i * \prod_{j /= i} P_j) + mht^U * \prod_i P_i) * hp^U
                    // U is exactly each of the varSet as key in table, all symbolic, except mht and hp
                    let mutable retF = FConst NUMERIC_ZERO
                    for e in table do
                        let e = e :?> DictionaryEntry
                        let varSet = e.Key :?> Set<NewVariable>
                        let _, mht, hp = e.Value :?> Hashtable * NumericType * NumericType
                        let varPart =
                            quickZeroOneRemoval
                                (Set.fold
                                    (fun nf nv ->
                                        nf + (FVar nv) * genProbProd false varSet (Some nv))
                                    (FConst NUMERIC_ZERO)
                                    varSet)
                        retF <- retF + (varPart + mht * (genProbProd false varSet None)) * hp
                    retAddTag (quickZeroOneRemoval retF)
                else
                    // target: construct formula of form: c * \prod P + \sum_i (\sum (c * \prod P)) * v_i
                    /// pre-part -- all mht * hp * \prod P here, also with constant v_i
                    let mutable prePart = FConst NUMERIC_ZERO
                    /// a map from variable (v_i) to coefficient (\sum (hp * \prod P)), allow c existence
                    let mutable varCoefficientMap = Map.empty
                    // \sum_U ((\sum_i v_i * \prod_{j /= i} P_j) + mht^U * \prod_i P_i) * hp^U
                    for e in table do
                        let e = e :?> DictionaryEntry
                        let varSet = e.Key :?> Set<NewVariable>
                        /// consPart:
                        ///    constant parts, constant E(Trips) and corresponding values,
                        ///    only constant parts are contained
                        /// the mht value, essentially (\sum_\pi \sigma(\pi)\prob(\pi)) / (\sum_\pi \prob(\pi))
                        /// hp, which is equal to (\sum_\pi \prob(\pi))
                        let consPart, mht, hp = e.Value :?> Hashtable * NumericType * NumericType
                        prePart <- prePart + mht * hp * genProbProd true varSet None
                        let iterFunc nv =
                            let res = consPart.[nv]
                            if res <> null then
                                let res = res :?> NumericType
                                if res <> Const.NUMERIC_MARK_NUMBER then
                                    prePart <- prePart + optimiseFormula (res * hp * genProbProd true varSet (Some nv))
                            else
                                let newToAdd = optimiseFormula (hp * genProbProd true varSet (Some nv))
                                match Map.tryFind nv varCoefficientMap with
                                | Some f ->
                                    varCoefficientMap <- Map.add nv (f + newToAdd) varCoefficientMap
                                | None ->
                                    varCoefficientMap <- Map.add nv newToAdd varCoefficientMap
                        Set.iter iterFunc varSet
                    done
                    let f =
                        Map.fold
                            (fun rf v f ->
                                rf + f * (FVar v))
                            prePart
                            varCoefficientMap
                    retAddTag (optimiseFormula f))
            (fun () -> (NUMERIC_ZERO, NUMERIC_ONE))
            // update config acc info
            // should make decision based on step count
            // bugfix : this kptsa is the normalised one given by the algorithm rather than the outside one
            (fun kptsa (q, m, gamma, p, op) (steps, curP) ->
                match kptsa.stepCount with
                | None ->
                    // None means every step to be count
                    (steps + NUMERIC_ONE, p * curP)
                | Some sc ->
                    match Map.tryFind (q, m, gamma, op) sc with
                    | Some ui -> (steps + ui, p * curP)
                    | None -> (steps, p * curP))
            // fold init value
            (fun _ consNvValue ->
                match consNvValue with
                | None -> Set.empty, Hashtable ()
                | Some pair -> foldConsNvValue (Set.empty, Hashtable ()) pair)
            // fold ret func
            (fun _ -> foldConsNvValue)
            retStandardForm
            // this must be normalised, the un-normalised version is wrong.
            true
            kptsa)


/// the expression to be computed
type Expr =
    | EAdd of Expr * Expr
    | EMul of Expr * Expr
    | EDiv of Expr * Expr
    | EMinus of Expr * Expr
    | EVar of int
    | EConst of NumericType
    
    static member (+) (f1, f2 : Expr) =
        EAdd (f1, f2)
    static member (*) (f1, f2 : Expr) =
        EMul (f1, f2)
    static member (-) (f1, f2 : Expr) =
        EMinus (f1, f2)
    static member (/) (f1, f2 : Expr) =
        EDiv (f1, f2)
    
    static member (*) (d : NumericType, f : Expr) =
        EMul (EConst d, f)
    static member (*) (f : Expr, d : NumericType) =
        EMul (f, EConst d)
    static member (+) (d : NumericType, f : Expr) =
        EAdd (EConst d, f)
    static member (+) (f : Expr, d : NumericType) =
        EAdd (f, EConst d)
    static member (-) (d : NumericType, f : Expr) =
        EMinus (EConst d, f)
    static member (-) (f : Expr, d : NumericType) =
        EMinus (f, EConst d)
    static member (/) (d : NumericType, f : Expr) =
        EDiv (EConst d, f)
    static member (/) (f : Expr, d : NumericType) =
        EDiv (f, EConst d)
    member e.ToString (varPrinter, constPrinter) =
        let printExpr (e : Expr) = e.ToString (varPrinter, constPrinter) in
        let secondOrderPrint e =
            match e with
            | EAdd _ | EMinus _ -> "(" + printExpr e + ")"
            | _ -> printExpr e
        let negPosPrint e =
            match e with
            | EConst _ | EVar _ -> printExpr e
            | _ -> "(" + printExpr e + ")"
        match e with
        | EAdd (e1, e2) ->
            printExpr e1 + " + " + printExpr e2
        | EMinus (e1, e2) ->
            printExpr e1 + " - " + negPosPrint e2
        | EMul (e1, e2) ->
            secondOrderPrint e1 + " * " + secondOrderPrint e2
        | EDiv (e1, e2) ->
            secondOrderPrint e1 + " / " + negPosPrint e2
        | EConst c ->
            if c < NUMERIC_ZERO then $"({constPrinter c})"
            else constPrinter c
        | EVar vi -> varPrinter vi
    member e.ToString varPrinter =
        let constPrinter (c : NumericType) =
            if Flags.DISPLAY_RATIONAL then c.ToString ()
            else $"""{c.ToString "f4"}"""
        e.ToString (varPrinter, constPrinter)
    override e.ToString () = e.ToString (fun x -> $"x{x}")
        

let rec optimiseExpr (e : Expr) : Expr =
    match e with
    | EAdd (e1, e2) ->
        match optimiseExpr e1, optimiseExpr e2 with
        | EConst c, e' when c = NUMERIC_ZERO -> e'
        | e', EConst c when c = NUMERIC_ZERO -> e'
        | EConst c1, EConst c2 -> EConst (c1 + c2)
        | EConst c1, EAdd (EConst c2, c2') ->
            EConst (c1 + c2) + c2'
        | EConst c1, EMinus (EConst c2, c2') ->
            EConst (c1 + c2) - c2'
        | EConst c1, EMinus (c2, EConst c2') ->
            EConst (c1 - c2') + c2
        | e1', e2' ->
            match e2' with
            | EConst _ -> optimiseExpr (e2' + e1')
            | _ -> e1' + e2'
    | EMul (e1, e2) ->
        match optimiseExpr e1, optimiseExpr e2 with
        | EConst c, _ when c = NUMERIC_ZERO -> EConst NUMERIC_ZERO
        | _, EConst c when c = NUMERIC_ZERO -> EConst NUMERIC_ZERO
        | EConst c, e' when c = NUMERIC_ONE -> e'
        | e', EConst c when c = NUMERIC_ONE -> e'
        | EConst c1, EConst c2 -> EConst (c1 * c2)
        | EConst c1, EMul (EConst c2, c2') ->
            (EConst (c1 * c2)) * c2'
        | EConst c1, EDiv (EConst c2, c2') ->
            (EConst (c1 * c2)) / c2'
        | EConst c1, EDiv (c2, EConst c2') ->
            (EConst (c1 / c2')) / c2
        | e1', e2' ->
            match e2' with
            | EConst _ -> optimiseExpr (e2' * e1')
            | EMul (EConst c, e2') -> optimiseExpr (c * (e1' * e2'))
            | _ -> e1' * e2'
    | EMinus (e1, e2) ->
        match optimiseExpr e1, optimiseExpr e2 with
        | e', EConst c when c = NUMERIC_ZERO -> e'
        | EConst c1, EConst c2 -> EConst (c1 - c2)
        | e1', e2' -> e1' - e2'
    | EDiv (e1, e2) ->
        match optimiseExpr e1, optimiseExpr e2 with
        | EConst c, _ when c = NUMERIC_ZERO -> EConst NUMERIC_ZERO
        | _, EConst c when c = NUMERIC_ZERO -> failwith "invalid operation -- divide by 0"
        | e', EConst c when c = NUMERIC_ONE -> e'
        | EConst c1, EConst c2 -> EConst (c1 / c2)
        | e1', e2' -> e1' / e2'
    | _ -> e
    
type ExprEnv<'v> =
    | EEPlus of ExprEnv<'v> list
    | EEMul of ExprEnv<'v> list
    | EEConst of NumericType
    | EEVar of 'v
type NormalisedExprAtom<'v> =
    | NormalisedExprAtom of NumericType * 'v list
/// every element of this type is bound to have shape:
/// \sum_i c_i * v_ij
/// where `c_i` is non-zero and for every `i`, the set of `v_ij` is unique
type NormalisedExpr<'v> =
    | NormalisedExpr of NormalisedExprAtom<'v> list
    
let sumNormalisedExprs lst =
    List.map (fun (NormalisedExpr lst) -> lst) lst
    |> List.concat
    |> List.fold (fun map (NormalisedExprAtom (nc, vs)) ->
            if nc = NUMERIC_ZERO then map
            else
                // this `sort` operation can already guarantee the normalisation of variable list
                // theoretically, `vs` should be a multi-set
                let vs = List.sort vs in
                match Map.tryFind vs map with
                | Some c -> Map.add vs (c + nc) map
                | None   -> Map.add vs nc map)
            Map.empty
    |> Map.toList
    |> List.map (fun (vs, c) -> NormalisedExprAtom (c, vs))
    |> NormalisedExpr
let distributeNormalisedExpr (NormalisedExpr l1) (NormalisedExpr l2) =
    List.allPairs l1 l2
    |> List.map (fun (NormalisedExprAtom (c1, vs1), NormalisedExprAtom (c2, vs2)) ->
        if c1 = NUMERIC_ZERO || c2 = NUMERIC_ZERO then []
        else [NormalisedExprAtom (c1 * c2, vs1 ++ vs2)])
    |> List.map NormalisedExpr
    |> sumNormalisedExprs
    
let rec normaliseExprEnv env =
    match env with
    | EEConst c  -> NormalisedExpr [NormalisedExprAtom (c, [])]
    | EEVar v    -> NormalisedExpr [NormalisedExprAtom (NUMERIC_ONE, [v])]
    | EEPlus lst -> sumNormalisedExprs $ List.map normaliseExprEnv lst
    | EEMul lst  -> List.reduce distributeNormalisedExpr $ List.map normaliseExprEnv lst
        
let rec eliminateMinus (e : Expr) =
    match e with
    | EAdd (e1, e2) -> EAdd (eliminateMinus e1, eliminateMinus e2)
    | EMul (e1, e2) -> EMul (eliminateMinus e1, eliminateMinus e2)
    | EDiv (e1, e2) -> EDiv (eliminateMinus e1, eliminateMinus e2)
    | EMinus (e1, e2) -> EAdd (eliminateMinus e1, EMul (EConst $ NUMERIC_ZERO - NUMERIC_ONE, eliminateMinus e2))
    | EConst _ | EVar _ -> e
    
let rec collectAddLevel (e : Expr) =
    match e with
    | EAdd (e1, e2) -> collectAddLevel e1 ++ collectAddLevel e2
    | _ -> [e]
let rec collectMulLevel (e : Expr) =
    match e with
    | EMul (e1, e2) -> collectMulLevel e1 ++ collectMulLevel e2
    | _ -> [e]
let rec toExprEnv e =
    match e with
    | EAdd _ -> List.map toExprEnv $ collectAddLevel e |> EEPlus
    | EMul _ -> List.map toExprEnv $ collectMulLevel e |> EEMul
    | EConst c -> EEConst c
    | EVar v -> EEVar v
    | EDiv _ -> failwith "Normalisation cannot cope with div."
    | EMinus _ -> IMPOSSIBLE "Minus should have been eliminated"
let fromNormalisedExpr (NormalisedExpr ats) =
    List.map (fun (NormalisedExprAtom (c, vs)) ->
        EConst c * (List.map EVar vs |> List.fold (*) (EConst NUMERIC_ONE))) ats
    |> List.fold (+) (EConst NUMERIC_ZERO)
    |> optimiseExpr
    
/// the strongest optimisation, the return value will of shape
/// \sum_i c_i * \pi_j v_ij
/// where for every `i`, there will be different `v_ij` set, which may be empty
let normaliseExpr (e : Expr) : Expr =
    let e = eliminateMinus e in
    toExprEnv e
    |> normaliseExprEnv
    |> fromNormalisedExpr
//    match e with
//    | EAdd _ ->
//        let adds = collectAddLevel e in
//        List.map normaliseExpr adds
//        |> List.fold (fun (rc, r) -> function | EConst c -> (c + rc, r) | rr -> (rc, rr :: r)) (NUMERIC_ZERO, [])
//        |> fun (c, lst) ->
//            if List.isEmpty lst then EConst c
//            else if c = NUMERIC_ZERO then List.reduce (+) lst
//            else EConst c + List.reduce (+) lst
//    | EMul _ ->
//        let muls = collectMulLevel e in
//        List.map normaliseExpr muls
//        |> List.fold (fun (rc, r) -> function | EConst c -> (c * rc, r) | rr -> (rc, rr :: r)) (NUMERIC_ONE, [])
//        |> fun (c, lst) ->
//            if List.isEmpty lst then EConst c
//            else if c = NUMERIC_ZERO then EConst NUMERIC_ZERO
//            else if c = NUMERIC_ONE then List.reduce (*) lst
//            else EConst c * List.reduce (*) lst
//    | EConst _ | EVar _ -> e
//    | EDiv _ -> failwith "Normalisation cannot cope with div."
//    | EMinus _ -> IMPOSSIBLE "Minus should have been eliminated"

/// Strongest optimisation to the equation system
/// Will result in a new equation system of form: v = \sum_i c_i * \pi_j v_ij
let normaliseExprSystem es =
    List.map (BiMap.sndMap normaliseExpr) es
    
let printExprVariable (vindex : int) : string =
    $"x{vindex}"

let rec private printExprWithVarPrinter (e : Expr) printExprVariable : string =
    e.ToString printExprVariable
        
let printExpr e = printExprWithVarPrinter e printExprVariable

let printExprSystem (l : (int * Expr) list) : string =
    let mutable ret = ""
    for i, e in l do
        ret <- ret + printExprVariable i + " = " + printExpr e + "\n"
    ret
    
let printExprSystemWithVarPrinter printVar es =
    Seq.map (fun (i, e) -> printVar i + $" = {printExprWithVarPrinter e printVar}") es
    |> String.concat "\n"
    
let printExprSystemWithVarMap es varMap =
    if Flags.NOT_PRINT_EQ_SYS then
        ""
    else
        let find = flip Map.find varMap in
        let printVar i = $"{find i}" in
        printExprSystemWithVarPrinter printVar es

/// give the formula system and a map
/// returns the equation system and an updated map
let formulaSystemToExprSystemWithHint<'v when 'v : comparison>
    (l : ('v * RawFormula<'v>) list)
    (fv2ev : Map<'v, int>) =
    let mutable fv2ev = fv2ev
    let mutable evCounter = fv2ev.Count
    let lookUpVarTable v =
        match fv2ev.TryFind v with
        | Some n -> n
        | None ->
            fv2ev <- Map.add v evCounter fv2ev
            evCounter <- evCounter + 1
            evCounter - 1
    let rec f2e (f : RawFormula<'v>) =
        match f with
        | FAdd (f1, f2) ->
            EAdd (f2e f1, f2e f2)
        | FMul (f1, f2) ->
            EMul (f2e f1, f2e f2)
        | FConst c -> EConst c
        | FVar v -> EVar (lookUpVarTable v)
    (List.map
        (fun (v, f) ->
            (lookUpVarTable v, f2e f))
        l, fv2ev)

let formulaSystemToExprSystem<'v when 'v : comparison>
    (x0 : 'v)
    (l : ('v * RawFormula<'v>) list)
    : (int * Expr) list =
    fst (formulaSystemToExprSystemWithHint l (Map(seq {x0, 0})))

let optimiseExprSystem es =
    List.map (fun (i, e) -> (i, optimiseExpr e)) es

type RatioFindSet = {
    representative : int
    equalRatioMap : Map<int, NumericType>
}
type RatioFindSetManager () =
    let mutable size = 0
    let mutable table : Map<int, RatioFindSet> = Map.empty
    
    let findOrAddNewFindSet vId =
        match Map.tryFind vId table with
        | None ->
            size <- size + 1
            let nfs = {
                representative = vId
                equalRatioMap = Map.add vId NUMERIC_ONE Map.empty
            }
            table <- Map.add vId nfs table
            nfs
        | Some fs -> fs
        
    let update vId nfs =
        Array.iter
            (fun id -> table <- Map.add id nfs table)
            (fst (Array.unzip (Map.toArray (Map.find vId table).equalRatioMap)))
    
    member x.recordNewRatio leftVId rightVId (ratio : NumericType) =
        let lfs = findOrAddNewFindSet leftVId
        let rfs = findOrAddNewFindSet rightVId
        let kl = Map.find leftVId lfs.equalRatioMap
        let kr = Map.find rightVId rfs.equalRatioMap
        // union the left set and the right set with the ratio
        // find a new representative, re-compute all ratio with respect to these two
        let little, big, linkingRatio =
            if lfs.representative < rfs.representative then
                lfs, rfs, kl / (kr * ratio)
            else
                rfs, lfs, (kr * ratio) / kl
        let nRatioMap =
            Map.fold
                (fun m id v -> Map.add id (v * linkingRatio) m)
                little.equalRatioMap
                big.equalRatioMap
        let nfs = {
            representative = little.representative
            equalRatioMap = nRatioMap
        }
        update leftVId nfs
        update rightVId nfs
    
    member x.tryFindRepresentativeAndRatio vId =
        match Map.tryFind vId table with
        | None -> None
        | Some fs ->
            Some (fs.representative, Map.find vId fs.equalRatioMap)
    member x.getSize () = size
    member x.getAllRepresentatives () =
        Map.fold
            (fun s _ (fs : RatioFindSet) -> Set.add fs.representative s)
            Set.empty
            table
    member x.isEmpty () = (size = 0)

/// conduct variable substitution to expression e
/// if not to substitute, just replace it with (fun idx -> EConst idx) 
let rec substituteVar tackleFunc (e : Expr) : Expr =
    let recall = substituteVar tackleFunc
    match e with
    | EAdd (e1, e2) ->
        EAdd (recall e1, recall e2)
    | EMul (e1, e2) ->
        EMul (recall e1, recall e2)
    | EDiv (e1, e2) ->
        EDiv (recall e1, recall e2)
    | EMinus (e1, e2) ->
        EMinus (recall e1, recall e2)
    | EVar vid -> tackleFunc vid
    | EConst _ -> e

/// get the list of expr that has the same order sorting by LHS
/// and the index of the new list is the new LHS variable
/// may vary the order
let reindexedExprSystem (es : (int * Expr) list) = 
    let ret = List.sortBy fst es
    let vlist = List.map fst ret
    /// re-parametrisation
    let reparaMap : Map<int, int> =
        Map.ofList (List.map swap (List.indexed vlist))
    let subsFunc vId = EVar (Map.find vId reparaMap)
    (List.map
        (fun (_, e) -> substituteVar subsFunc e)
        ret, Array.ofList vlist)
    

let rec computeExpr expr (values : NumericType list) : NumericType =
    let recall e =
        computeExpr e values
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
    | EVar v -> values.[v]

/// if the current value should be round up, it will do the job.
let computeExprList (l : Expr list) values =
    let values =
        if Flags.ALLOW_ITER_ROUND_UP then
            List.map NumericType.RoundUp values
        else values
    List.map
        (fun expr ->
            computeExpr expr values)
        l

type FixedPointType =
    | FPTLeast
    | FPTGreatest
    
/// returns the zero variable list and the rest equation system
let iterToFindLFPZeroVariables es =
    let nes, remap = reindexedExprSystem es
    let computeRet values = computeExprList nes values
    let values =
        let initValues =
            List.init es.Length $ fun _ -> NUMERIC_ZERO
        in
        computeRet initValues
    let finalValues =
        // just need n times, where n is the variable number, do not require value of ret
        fst (List.fold
                 (fun (r, count) _ ->
                    if Flags.INNER_DEBUG then
                        Console.Write $"\rFourth kind filter run for {count} times."
                    (computeRet r, count + 1)) (values, 0) es) in
    List.zip nes finalValues
    |> List.indexed
    |> List.partition (snd >> snd >> (=) NUMERIC_ZERO)
    // the first part is the variables to remove
    |> BiMap.fstMap (List.map (fst >> Array.get remap))
    |> BiMap.sndMap (List.map (fun (idx, (e, _)) ->
        (remap[idx], substituteVar (Array.get remap >> EVar) e)))
//    |> aggregateList (fun (idx, (e, final)) ->
//        let ret = (remap[idx], substituteVar (Array.get remap >> EVar) e) in
//        (final = NUMERIC_ZERO, ret))
//    |> List.partition fst

/// promise not to change the original equation system index, only removing, not changing
///
/// 
/// 
/// replace the variables that:
/// kind 1:
///     v = c
///     v = c * v + c' -> v = c' / (1 - c)
///     v = c * v { c /= 1 } -> v = 0
///     v = v -> v = 0 { LFP } | v = 1 { GFP }
///     // v = c * v' { v < v' }  -- this then handles already the kind 2 below
///                               -- this method will also work for kind 2
///                               -- currently remove this kind, as there may be troubles
/// kind 2:
///     v = c * v'
/// kind 3:
///     variables that have exactly the same RHS
/// kind 4:
///     erase by iteration
/// kind 5:
///     v = f(v) & v' = f(v') -> v = v'
let simplifyExprSystem fpType (es : (int * Expr) list) =
    let es = optimiseExprSystem es
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
                recordInfo i (EConst $ match fpType with
                                       | FPTLeast -> NUMERIC_ZERO
                                       | FPTGreatest -> NUMERIC_ONE)
                false
//            else if i < vi then
//                recordInfo i e
//                false
            else true
        | EMul (EConst _, EVar vi) ->
            if vi = i then
                recordInfo i (EConst NUMERIC_ZERO)
                false
//            else if i < vi then
//                recordInfo i e
//                false
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
    
//    /// v = v'
    let secondKindFilter recordInfo (i, e) =
        match fpType with
        | FPTGreatest -> true  // do not filter the second kind for the greatest case
        | FPTLeast ->
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
        changed <- true
        while changed do
            changed <- false
            round <- round + 1
            
            debugPrint $"Conduct round {round} simplification..."
            
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
                ret <- optimiseExprSystem ret
            
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
                debugPrint $"There are {firstKindMap.Count} first kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + firstKindMap.Count
            end
            
            // the following kind is handled by the first kind above
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
                
                debugPrint $"There are {findSets.getSize ()} second kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + findSets.getSize ()
            end
            
            // filter third kind -- has exactly the same RHS
            begin
                let mutable replaceMap = Map.empty
                ret <- flip List.map ret $ BiMap.sndMap normaliseExpr
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
                debugPrint $"There are {replaceMap.Count} third kind trivial variables filtered out."
                totallyErasedVar <- totallyErasedVar + replaceMap.Count
            end
            
            // filter fifth kind
            begin
                let replaceMap, newRet =
                    let placeHolderIdx = -2 in
                    // the equation system where for v = f(v), the f has special placeholderIdx for v
                    let subsEqSys =
                        let subsFunc targetI thisI =
                            if thisI = targetI then EVar placeHolderIdx
                            else EVar thisI
                        in
                        flip List.map ret (fun (i, e) ->
                            (i, normaliseExpr $ substituteVar (subsFunc i) e))
                        |> List.sortWith (fun (i, e) (i', e') ->
                            match compare e e' with
                            | 0 -> compare i i'
                            | c -> c)
                    in
                    let foldFunc (mapList, newRet) (i : int, e : Expr) =
                        match newRet with
                        | (i', e') :: _ ->
                            if e = e' then changed <- true; ((i, i') :: mapList, newRet)
                            else (mapList, (i, e) :: newRet)
                        | [] -> ([], [(i, e)])
                    in
                    // substitute back to the target variable
                    let subsBackFunc targetI thisI =
                        if thisI = placeHolderIdx then EVar targetI
                        else EVar thisI
                    in
                    List.fold foldFunc ([], []) subsEqSys
                    |> BiMap.fstMap Map.ofSeq
                    |> BiMap.sndMap (List.map (fun (i, e) -> (i, substituteVar (subsBackFunc i) e)))
                in
                ret <- newRet;
                let mutable replaceMap = replaceMap in
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
                debugPrint $"There are {replaceMap.Count} fifth kind trivial variables filtered out."
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
                List.init ret.Length $ fun _ ->
                    match fpType with
                    | FPTLeast -> NUMERIC_ZERO
                    | FPTGreatest -> NUMERIC_ONE
            in
            // the initial value should be (n + 1) times
            List.fold (fun value _ -> computeRet value) (computeRet initValues) ret
        let finalValues =
            // just need n times, where n is the variable number, do not require value of ret
            fst (List.fold
                     (fun (r, count) _ ->
                        innerDebugSameLinePrint $"\rFourth kind filter run for {count} times.    "
                        (computeRet r, count + 1)) (values, 0) ret)
        let mutable fourthCount = 0 in
        let nRes =
            List.zip values finalValues
            |> List.zip nes
            |> List.map (fun (e, (init, final)) ->
                if init = final then begin
                    fourthCount <- fourthCount + 1;
                    EConst final
                end
                else e)
            |> List.indexed
            |> List.map
                   (BiMap.pairMap
                        (Array.get remap,
                         substituteVar (Array.get remap >> EVar)))
        in
        
//        let mutable eraseMap = Map.empty
//        ret <-
//            let ret = List.indexed nes
//            let filterFunc ((initVal, finalVal), (i, _)) =
//                if finalVal = NUMERIC_ZERO then
//                    eraseMap <- Map.add i NUMERIC_ZERO eraseMap
//                    false
//                elif initVal = finalVal then
//                    eraseMap <- Map.add i finalVal eraseMap
//                    false
//                else true
//            let remainRet =
//                snd (List.unzip (List.filter filterFunc (List.zip (List.zip values finalValues) ret)))
//            changed <- not (Map.isEmpty eraseMap)
//            match Map.tryFind 0 eraseMap with
//            | Some c ->
//                changed <- false
//                [0, EConst c]
//            | None ->
//                let subsFunc vId =
//                    match Map.tryFind vId eraseMap with
//                    | Some c -> EConst c
//                    | None -> EVar vId
//                List.map (fun (i, e) -> (i, substituteVar subsFunc e)) remainRet
//        printfn ""  // to change line
        debugPrint $"Found {fourthCount} fourth kind trivial variables."
        ret <- nRes
        // there are no variable filtered out, but just found, 
//        totallyErasedVar <- totallyErasedVar + fourthCount
//        ret <- List.map (fun (i, e) -> (i, optimiseExpr e)) ret
//        
//        // remap ret
//        ret <- List.map (fun (i, e) -> (remap[i], substituteVar (fun i -> EVar remap[i]) e)) ret 
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
    begin
        // firstly collect all relevant variables
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
        // then remove all irrelevant ones
        ret <-
            List.fold
                (fun rl (vId, rBody) ->
                    if relevantVars.Contains vId then
                        (vId, rBody) :: rl
                    else rl)
                []
                (List.indexed riRet)
        debugPrint $"Erased {erasedVariables} Irrelevant Variables."
        totallyErasedVar <- totallyErasedVar + erasedVariables
        
        // remap vars
        ret <- List.map (fun (i, e) -> (remap[i], substituteVar (fun i -> EVar remap[i]) e)) ret
    end
    
    debugPrint $"Totally Erased Variables by Simplification: {totallyErasedVar}."
    
    ret

type TransRuleList =
    (State * LocalMemory * Gamma * NumericType * TransOp) list

/// let the specified q, m, and gamma all be the start symbols in l
let refreshIndexInTransRuleList state memory gamma l =
    let refreshTarget tar now =
        if now = tar then 0
        elif now = 0 then tar
        else now
    let refreshQ = refreshTarget state
    let refreshM = refreshTarget memory
    let refreshGamma = refreshTarget gamma
    let refreshElement (q, m, gamma, p, op) =
        let updatedOp =
            match op with
            | TransUp (q', m', gamma') ->
                TransUp (
                     refreshQ q',
                     refreshM m',
                     refreshGamma gamma'
                )
            | TransDown (q', m') ->
                TransDown (
                    refreshQ q',
                    refreshM m'
                )
            | TransState q' ->
                TransState (refreshQ q')
            | _ -> op
        (refreshQ q,
         refreshM m,
         refreshGamma gamma,
         p,
         updatedOp)
    List.map
        refreshElement
        l
    
module NewCompute = begin
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
        
    type DoubleExpr =
        | DAdd of DoubleExpr * DoubleExpr
        | DMul of DoubleExpr * DoubleExpr
        | DVar of int
        | DConst of double
        static member fromExpr e =
            match e with
            | EVar vId -> DVar vId
            | EConst c -> DConst $ c.getDouble ()
            | EAdd (e1, e2) -> DAdd (DoubleExpr.fromExpr e1, DoubleExpr.fromExpr e2)
            | EMul (e1, e2) -> DMul (DoubleExpr.fromExpr e1, DoubleExpr.fromExpr e2)
            | _ -> failwith "Not Support type of operation"
    let rec computeDoubleExpr d (value : double[]) =
        let recall d = computeDoubleExpr d value in
        match d with
        | DAdd (d1, d2) -> recall d1 + recall d2
        | DMul (d1, d2) -> recall d1 * recall d2
        | DConst c      -> c
        | DVar vId      -> value[vId]
    let computeDoubleExprArray ds value =
        Array.map (flip computeDoubleExpr value) ds
end

/// minDiff : minimum difference
/// just measure the increase, NOT accuracy
let iteratingExprSystem
    (es : (int * Expr) list)
    (maxIterRound : uint64 option)
    (minDiff : NumericType) : (int * NumericType) [] * uint64 =
    // get re-indexed equations system with LHS removed -- the index of this array is the LHS subscript.
    let mutable times = 0uL in
    let rec iterate exprs vals =
        checkTimeOut ();
        let exceedMaxTimes =
            match maxIterRound with
            | None          -> false
            | Some maxRound -> times > maxRound in
        times <- times + 1uL;
        if exceedMaxTimes then vals
        else
            let nextVals =
                NewCompute.computeExprArray exprs vals
//                |> Array.map (fun x ->
//                    if x < NUMERIC_ZERO then IMPOSSIBLE ()
//                    elif boundOne && x > NUMERIC_ONE then NUMERIC_ONE
//                    else x)
            in
            Array.zip nextVals vals
            |> Array.map (uncurry (-) >> abs)
            |> Array.max
            |> fun x ->
                if Flags.DEBUG then begin
                    printf $"\rIteration Rounds: {times}, Max Diff: {x.getDouble ()}   ";
                end;
                if x <= minDiff then nextVals else iterate exprs nextVals
        in
    let exprs, oriVList =
        reindexedExprSystem es
        |> BiMap.fstMap Array.ofList
    in
    let initVals = Array.map (fun _ -> NUMERIC_ZERO) exprs in
    iterate exprs initVals
    |> Array.indexed
    |> Array.map (BiMap.fstMap (Array.get oriVList))
    |> fun x -> (x, times)
//    let rec approximate (values : NumericType list) times =
//        checkTimeOut ()
//        if Flags.DEBUG = true then
//            Console.Write $"\rIteration for the {times} time            "
//            if Flags.PRINT_ITER_VALUES then
//                printfn "\nvalues are:"
//                List.iter
//                    (fun (i, v) ->
//                        printfn $"\tx{i} = {v}")
//                    (List.indexed values)
//        let approxValues =
//            computeExprList l values
//        let curDiff =
//            List.max
//                (List.map (fun (e1, e2) -> e1 - e2)
//                    (List.zip approxValues values))
//        let tryRet () =
//            if curDiff <= minDiff then
//                if Flags.DEBUG = true then
//                    printfn $"\nIterated for {times} times."
//                approxValues
//            else approximate approxValues (times + uint64 1)
//        match maxIterRound with
//        | None -> tryRet ()
//        | Some maxTimes ->
//            if times >= maxTimes then
//                if Flags.DEBUG = true then
//                    printfn $"\nIterated for {times} times."
//                approxValues
//            else tryRet ()
//    List.zip (Array.toList reparaMap) (approximate tilde0 (uint64 0))

/// there may be some redundant rules after epsilon elimination
/// because there will not be any epsilon transition any more
/// This function should only call for those without any epsilon transition
/// otherwise, exception will be raised.
let reduceRedundantKPTSARule maxState rules =
    // a state to be reachable must be mentioned in Down or Up
    let usedStates = Array.create (maxState + 1) false
    usedStates.[0] <- true
    /// this function explore all used states by the rest rules -- those have been iterated don't need to
    /// be further tackled, we have the thisKindSet as the first to explored
    let rec exploreUsedStates restRules thisSet =
        if Set.isEmpty thisSet then ()
        else
            let mutable nextSet = Set.empty
            let filterFunc (q, _, _) lst =
                // they're not for this time, leave them for further use
                if not (Set.contains q thisSet) then true
                else
                    let iterFunc (_, op) =
                        let dealWithQ q =
                            if not usedStates.[q] then
                                usedStates.[q] <- true
                                nextSet <- Set.add q nextSet
                        match op with
                        | TransDiv | TransTer -> ()
                        | TransState _ -> failwith "Epsilon Elimination Error."
                        | TransUp (q, _, _) -> dealWithQ q
                        | TransDown (q, _) -> dealWithQ q
                    List.iter iterFunc lst
                    false
            let nextRules = Map.filter filterFunc restRules
            exploreUsedStates nextRules nextSet
    
    exploreUsedStates rules (Set.add 0 Set.empty)
    
    Map.filter (fun (q, _, _) _ -> usedStates.[q]) rules

/// algorithm from [Mehryar Mohri] "Semiring Frameworks and Algorithms for Shortest-Distance Problems".
/// please refer to this paper for justification.
/// A simple version -- just for those without loop, because if with loop, this algorithm will just compute
/// near result and the generated rational is hard to compute.
/// As this algorithm is fundamentally an algorithm that will only end when there is tolerant for zero if has loop
let epsilonElimination_Simple (kptsa : KPTSA) =
    debugPrint "Epsilon elimination begins ..."
    let mutable rules = Map.empty
    let iterFunc (s, m, gamma) _ : unit =
        checkTimeOut "In Epsilon Elimination"
        let mutable nl = List.empty
        let mutable debugRoundCount = 0
        let distances =
            let mutable dis : Map<State, NumericType> = Map.add -1 NUMERIC_ONE Map.empty
            let mutable rmap : Map<State, NumericType> = Map.add -1 NUMERIC_ONE Map.empty
            let findMap q (m : Map<State, NumericType>) : NumericType =
                match Map.tryFind q m with
                | None -> NUMERIC_ZERO
                | Some s -> s
            let mutable todo : Queue<State> = Queue<State> [-1]
            while todo.Count > 0 do
                let q = todo.Dequeue ()
                debugRoundCount <- debugRoundCount + 1
                let R = findMap q rmap
                rmap <- Map.add q NUMERIC_ZERO rmap
                let iterFunc (p, op) : unit =
                    match op with
                    | TransState q' ->
                        let nextDistance = (findMap q' dis) + (R * p)
                        // use near equal rather than equal, because this is just an approximation method
                        if not ((R * p) =~= NUMERIC_ZERO) then
                            dis <- Map.add q' nextDistance dis
                            rmap <- Map.add q' ((findMap q' rmap) + (R * p)) rmap
                            if todo.Contains q' then ()
                            else todo.Enqueue q'
                    | _ -> ()
                let enhancedOriRules = Map.add (-1, m, gamma) [(NUMERIC_ONE, TransState s)] kptsa.delta
                match Map.tryFind (q, m, gamma) enhancedOriRules with
                | None -> ()
                | Some tl -> List.iter iterFunc tl
            
            dis <- Map.add -1 NUMERIC_ONE dis
            
            dis
        
        innerDebugPrint $"The computation for (q{s}, m{m}, gamma{gamma}) takes {debugRoundCount} rounds."
        
        let iterFunc q d : unit =
            match Map.tryFind (q, m, gamma) kptsa.delta with
            | None -> ()
            | Some tl ->
                let iterFunc (p, op) =
                    match op with
                    | TransState _ -> ()
                    | _ -> nl <- (p * d, op) :: nl
                
                List.iter iterFunc tl
        Map.iter iterFunc distances
        
        let duplicateElimination (l : (NumericType * TransOp) list) =
            let rec eliminateNearbyDuplicate l =
                match l with
                // has >= 2 elements
                | (p, op) :: (p', op') :: l' ->
                    if op = op' then
                        eliminateNearbyDuplicate ((p + p', op) :: l')
                    else
                        (p, op) :: eliminateNearbyDuplicate ((p', op') :: l')
                // has < 2 elements
                | [(p, op)] -> [(p, op)]
                | [] -> []
            eliminateNearbyDuplicate (List.sortBy snd l)
        nl <- duplicateElimination nl
        rules <- Map.add (s, m, gamma) nl rules
    Map.iter iterFunc kptsa.delta
    
    // this is too an over-approximation, for we only want those mentioned
    // in the path from q0, as q is the one passed around continuously, there is no need to consider local stuff
//    Map.iter
//        (fun _ ->
//            List.iter
//                (fun (_, op) ->
//                    match op with
//                    | TransDiv | TransTer -> ()
//                    | TransState _ -> failwith "Epsilon Elimination Error."
//                    | TransUp (q, _, _) -> usedStates.[q] <- true
//                    | TransDown (q, _) -> usedStates.[q] <- true))
//        rules
        
    rules <- reduceRedundantKPTSARule kptsa.maxState rules
    
    
    debugPrint "epsilon elimination ends."
    
    {
        kptsa with
            delta = rules
    }

/// an exact way to conduct epsilon elimination, but this is quite expensive
/// it can cope with loops exactly
let epsilonElimination_Exact copeWithStepCount (kptsa : KPTSA) =
    let stepCounts =
        if copeWithStepCount then
            match kptsa.stepCount with
            | Some sc -> sc
            | None ->
                Map.fold
                    (fun rm (q, m, gamma) ->
                        List.fold
                            (fun rm (_, op) -> Map.add (q, m, gamma, op) NUMERIC_ONE rm)
                            rm)
                    Map.empty
                    kptsa.delta
        else Map.empty
    /// those in this map should have no epsilon transitions
    /// use this as much as possible rather than kptsa.delta -- this can avoid repeating computation
    let mutable rules = Map.empty
    let mutable nStepCounts = Map.empty
    let copeWithEpsilon q m gamma =
        /// q and varId map, variable to solve the linear equation
        let qVarMap = IndexingTable ()
        /// the matrix information, for each dimension, add the corresponding parameters to the other variables
        let mutable matrixInfo : Map<int, Map<int, NumericType>> = Map.empty
        /// target nodes with dimension information
        /// the int is variable ID with corresponding parameter
        /// remember to change the sign of the numeric type in vector forming
        let mutable tarNodes : Map<TransOp, Map<int, NumericType>> = Map.empty
        let exploredQ = HashSet<State> ()
        let addToMap outerKey innerKey value map assignFunc =
            let m =
                match Map.tryFind outerKey map with
                | Some m -> m
                | None -> Map.empty
            assignFunc (Map.add outerKey (Map.add innerKey value m) map)
        let addToTarNodes op varId p =
            addToMap op varId p tarNodes (fun nmap -> tarNodes <- nmap)
        let addToMatrixInfo cId tId p =
            addToMap cId tId p matrixInfo (fun nmap -> matrixInfo <- nmap)
        
        /// the explore driven queue
        let qToExplore = Queue<State> ()
        exploredQ.Add q |> ignore
        qToExplore.Enqueue q
        
        while qToExplore.Count > 0 do
            let q = qToExplore.Dequeue ()
            let varId = qVarMap.lookUp q
            match Map.tryFind (q, m, gamma) rules with
            | Some lst ->
                List.iter
                    (fun (p, op) -> addToTarNodes op varId p)
                    lst
            | None ->
                match Map.tryFind (q, m, gamma) kptsa.delta with
                | Some lst ->
                    List.iter
                        (fun (p, op) ->
                            match op with
                            | TransState q' ->
                                if not (exploredQ.Contains q') then
                                    qToExplore.Enqueue q'
                                    exploredQ.Add q' |> ignore
                                addToMatrixInfo varId (qVarMap.lookUp q') p
                            | _ -> addToTarNodes op varId p)
                        lst
                | None -> ()
        
        let idQMap = fst (Array.unzip (Array.sortBy snd (Map.toArray (qVarMap.getRawMap ()))))
        let matrixDimension = qVarMap.getNextIndex ()
        
        let generateArrayFromInfo info =
            let initFunc vId =
                match Map.tryFind vId info with
                | Some p -> p
                | None -> NUMERIC_ZERO
            Array.init matrixDimension initFunc
        
        /// generate a gaussian solver for a given B, compute Ax = B
        /// as A is fixed, the method of computing B is thus generated from here
        let getGaussianSolver (A : NumericType [][]) =
            // A can be destroyed in the current context, but it is not a good habit to do that
            // but also, we did not check if this really works
            /// the A to use, not destroying the original A
            let A = Array.map Array.copy A
//            let B = Array.copy B
            // forward computation
            let funcQueue = Queue<NumericType [] -> NumericType []> ()
            // protect the given B from being destroyed
            funcQueue.Enqueue (fun B -> Array.copy B)
            for i in 0 .. A.Length - 1 do
                for j in i + 1 .. A.Length - 1 do
                    // A.[i].[i] should never be 0 as only when infinite self-looping can make this possible
                    // but this is erased beforehand
                    let c = A.[j].[i] / A.[i].[i]
                    A.[j].[i] <- NUMERIC_ZERO
                    for k in i + 1 .. A.Length - 1 do
                        A.[j].[k] <- A.[j].[k] - (c * A.[i].[k])
                    funcQueue.Enqueue
                        (fun B ->
                            B.[j] <- B.[j] - (c * B.[i])
                            B)
            // backward substitution
            for i = A.Length - 1 downto 0 do
                let c = A.[i].[i]
                if c <> NUMERIC_ZERO then
                    funcQueue.Enqueue
                        (fun B ->
                            B.[i] <- B.[i] / c
                            B)
                    for j = i - 1 downto 0 do
                        let c' = A.[j].[i]  // A.[i].[i] should be regard as 1 here as B.[i] is the updated one
                        A.[j].[i] <- NUMERIC_ZERO
                        funcQueue.Enqueue
                            (fun B ->
                                B.[j] <- B.[j] - (c' * B.[i])
                                B)
                else
                        funcQueue.Enqueue
                         (fun B ->
                            if B.[i] <> NUMERIC_ZERO then
                                failwith "Invalid Parameter -- no solution to this equation system."
                            else B)
            
            let funcArr = funcQueue.ToArray ()
//            B
            fun B ->
                Array.fold
                    (fun B f -> f B)
                    B
                    funcArr
        
        let stepCountVectorBase =
            if copeWithStepCount then
                Array.init matrixDimension
                    (fun rowId ->
                        match Map.tryFind rowId matrixInfo with
                        | Some colInfo ->
                            Map.fold
                                (fun rv colId prob ->
                                    match Map.tryFind
                                            (idQMap.[rowId], m, gamma, TransState idQMap.[colId])
                                            stepCounts with
                                    | Some sc -> rv - sc * prob
                                    | None -> rv)
                                NUMERIC_ZERO
                                colInfo
                        | None -> NUMERIC_ZERO)
//                let mutable ret = Array.create matrixDimension NUMERIC_ZERO
//                Array.iter
//                    (fun (rowId, columnInfo) ->
//                        ret.[rowId] <-
//                            Map.fold
//                                (fun rv colId prob ->
//                                    match Map.tryFind
//                                            (idQMap.[rowId], m, gamma, TransState idQMap.[colId])
//                                            stepCount with
//                                    | Some sc -> rv - sc * prob
//                                    | None -> rv)
//                                NUMERIC_ZERO
//                                columnInfo)
//                    sortedMatrixInfo
//                ret
            else Array.empty
        
        // after exploration, solve equation for each dimension
        // firstly generate the matrix from matrixInfo
        let gaussianSolver =
            let A =
                Array.init matrixDimension
                    (fun rowId ->
                        let res =
                            match Map.tryFind rowId matrixInfo with
                            | Some colInfo -> generateArrayFromInfo colInfo
                            | None -> Array.create matrixDimension NUMERIC_ZERO
                        res.[rowId] <- res.[rowId] - NUMERIC_ONE
                        res)
                // bugfix : the following code to initialise A may cause A of less dimension than it should
//                Map.iter
//                    (fun rowId columnInfo ->
//                        let res =
//                            generateArrayFromInfo columnInfo
//                        // should -1, because the LHS is shifted to RHS
//                        res.[rowId] <- res.[rowId] - NUMERIC_ONE
//                        ret.[rowId] <- res)
//                    matrixInfo
            getGaussianSolver A
        let mutable tmpRules = Map.empty
        let addToTmpRules op (vId, p) =
            if p > NUMERIC_ZERO then
                let lst =
                    match Map.tryFind (idQMap.[vId], m, gamma) tmpRules with
                    | Some lst -> lst
                    | None -> []
                tmpRules <- Map.add (idQMap.[vId], m, gamma) ((p, op) :: lst) tmpRules
        let addToStepCounts op (rowId, steps) =
            if steps > NUMERIC_ZERO then
                if Flags.INNER_DEBUG then
                    match Map.tryFind (idQMap.[rowId], m, gamma, op) nStepCounts with
                    | Some s ->
                        if s <> steps then failwith "Conflict step count number added."
                    | None -> ()
                nStepCounts <- Map.add (idQMap.[rowId], m, gamma, op) steps nStepCounts
        let generateVector vecInfo =
            // reverse all constants as constants are shifted from RHS to LHS
            Array.map (fun e -> NUMERIC_ZERO - e) (generateArrayFromInfo vecInfo)
        let generateStepCountVector op rowInfo =
            // do not affect the base prototype
            // let it be driven by Map rather than mapping base
            // complexity reduce from O(n log m) to O(n + m)
            let baseVec = Array.copy stepCountVectorBase
            Map.iter
                (fun rowId rowVal ->
                    let key = (idQMap.[rowId], m, gamma, op)
                    let sc =
                        match Map.tryFind key nStepCounts with
                        | Some sc -> sc
                        | None ->
                            match Map.tryFind key stepCounts with
                            | Some sc -> sc
                            | None -> NUMERIC_ZERO
                    baseVec.[rowId] <- baseVec.[rowId] - sc * rowVal)
                rowInfo
            baseVec
        flip Map.iter tarNodes (fun op vectorInfo ->
            let vec = generateVector vectorInfo in
            let res = gaussianSolver vec in
            // debug: should save rules to a temporary place rather than changing `rules` variable directly
            // note: it is definitely not a good practice to use mutable variables
            Array.iter (addToTmpRules op) (Array.indexed res);
            if copeWithStepCount then
                let scVec = generateStepCountVector op vectorInfo
                let scRes = gaussianSolver scVec
                Array.iter (addToStepCounts op) (Array.indexed
                     (Array.map
                          (fun (pd, pb) ->
                            if pb <> NUMERIC_ZERO then
                                pd / pb
                            else NUMERIC_ZERO)
                          (Array.zip scRes res))));
        // add the temporary rules back to rules itself
        flip Seq.iter (Map.toSeq tmpRules) (fun (config, lst) ->
            rules <- flip (Map.change config) rules (Option.defaultValue lst >> Some))
        
            
        
    for (q, m, gamma), lst in Map.toArray kptsa.delta do
        // it is possible that this key has already been added to rules if it is within other loops
        if not (Map.containsKey (q, m, gamma) rules) then
            // optimisation: distinguish between those with or without epsilon transition
            // check if there is any epsilon transition from this node
            // bugfix: new rules may be additionally added to those already that are stable
            //         so rules in the epsilon elimination progressing should firstly add to a temporary place
            try
                rules <-
                    Map.add
                        (q, m, gamma)
                        (List.fold
                            (fun ret (p, op) ->
                                match op with
                                | TransState q' when q' = q && p = NUMERIC_ONE ->
                                    // this kind of infinite self-looping should be erased
                                    ret
                                // just a mark, not stand for its meaning
                                | TransState _ -> raise (NFMarkException x0New)
                                | _ -> (p, op) :: ret)
                            []
                            lst)
                        rules
            with
            | NFMarkException _ -> copeWithEpsilon q m gamma
    
    // if there is no rule for (q0, m0, gamma0), then there should be only one div rule
    if Map.tryFind (0, 0, 0) rules = None then
        rules <- Map.add (0, 0, 0) [NUMERIC_ONE, TransDiv] Map.empty
    else
        rules <- reduceRedundantKPTSARule kptsa.maxState rules
    
    if copeWithStepCount then
        Map.iter
            (fun key steps ->
                let _, _, _, op = key
                match op with
                | TransState _ -> ()
                | _ ->
                    match Map.tryFind key nStepCounts with
                    | Some _ -> ()
                    | None -> nStepCounts <- Map.add key steps nStepCounts
                )
            stepCounts
    
    let stepCounts =
        if copeWithStepCount then
            Some nStepCounts
        else None
    
    {
        kptsa with
            delta = rules
            stepCount =
                if copeWithStepCount then stepCounts
                else kptsa.stepCount
    }

/// an automatic function, first judge if there is looping dependency
///     > if there is, put it into "Exact" version
///     > or, put it into "Simple" version
/// note that this judgement itself will cost something, if the property is known, like from PAHORS
/// one should put the K-PTSA into the right function rather than this function.
let epsilonElimination alsoForStepCounts (kptsa : KPTSA) =
    if alsoForStepCounts || KPTSA.EpsilonLoopDetect kptsa then
        epsilonElimination_Exact alsoForStepCounts kptsa
    else
        epsilonElimination_Simple kptsa

// a wrong version, because meeting the same current (q, m, gamma) cannot guarantee the absence of behavior
// like down with state to a new place
//let removeUnreachableRules (kptsa : KPTSA) =
//    let mutable rules = Map.empty
//    // after epsilon elimination, the rules may contain some unreachable rules
//    let curRules = kptsa.delta
//    // gamma0 |-> m0
//    let initialTreeStack = Map.add [0] 0 Map.empty
//    let rec tsaSimulation state treeStack tPointer =
//        let q = state
//        let m = Map.find tPointer treeStack
//        let gamma, lowerTP =
//            match tPointer with
//            | cg :: ltp -> cg, ltp
//            | _ -> failwith "Impossible"
//        if rules.ContainsKey (q, m, gamma) then ()
//        else
//            let ruleList =
//                match Map.tryFind (q, m, gamma) curRules with
//                | None -> []
//                | Some l ->
//                    rules <- Map.add (q, m, gamma) l rules
//                    l
//            for _, op in ruleList do
//                match op with
//                | TransTer -> ()
//                | TransDiv -> ()
//                | TransState _ -> failwith "Epsilon Elimination Error -- contains epsilon."
//                | TransUp (q', m', gamma') ->
//                    let ntp = gamma' :: tPointer
//                    let nts =
//                        if treeStack.ContainsKey ntp then
//                            Map.add tPointer m' treeStack
//                        else
//                            Map.add tPointer m' (Map.add ntp 0 treeStack)
//                    tsaSimulation q' nts ntp
//                | TransDown (q', m') ->
//                    let nts = Map.add tPointer m' treeStack
//                    tsaSimulation q' nts lowerTP
//    
//    tsaSimulation 0 initialTreeStack [0]
//    
//    {
//        kptsa with
//            delta = rules
//    }

// wrong version again -- cannot trace all the possible loops
//let newEpsilonElimination (kptsa : KPTSA) =
//    let mutable rules = Map.empty
//    // for each sub-rule, trace the rule set
//    let iterFunc (q, m, gamma) _ : unit =
//        let mutable nl = List.empty
//        let rec trace cof q' traceStack =
//            let mutable curRecord = []
//            let iterFunc (p : NumericType, op) =
//                match op with
//                | TransState nq ->
//                    let newTraceStack = (q', p, curRecord) :: traceStack
//                    let rec backwardTracing (cof : NumericType) stack =
//                        match stack with
//                        | [] -> None
//                        | (cq, cp, cr) :: s' ->
//                            if cq = nq then
//                                if cof * cp >= 1.0 then None
//                                else
//                                    List.iter
//                                        (fun (p, op) ->
//                                        nl <- (cof * cp * p / (1.0 - cof * cp), op) :: nl)
//                                        cr
//                                    Some (cof * cp)
//                            else
//                                match backwardTracing (cof * cp) s' with
//                                | None -> None
//                                | Some lp ->
//                                    List.iter
//                                        (fun (p : NumericType, op) ->
//                                        nl <- (cof * cp * p / (1.0 - cof * cp), op) :: nl)
//                                        cr
//                                    Some lp
//                    match backwardTracing 1.0 newTraceStack with
//                    | Some _ -> ()
//                    | None -> trace (p * cof) nq newTraceStack
//                | _ ->
//                    nl <- (cof * p, op) :: nl
//                    curRecord <- (cof * p, op) :: curRecord
//            match Map.tryFind (q', m, gamma) kptsa.delta with
//            | None -> ()
//            | Some tl ->
//                List.iter
//                    iterFunc
//                    tl
//        trace 1. q []
//        
//        let duplicateElimination (l : (NumericType * TransOp) list) =
//            let rec eliminateNearbyDuplicate l =
//                match l with
//                // has >= 2 elements
//                | (p, op) :: (p', op') :: l' ->
//                    if op = op' then
//                        eliminateNearbyDuplicate ((p + p', op) :: l')
//                    else
//                        (p, op) :: eliminateNearbyDuplicate ((p', op') :: l')
//                // has < 2 elements
//                | [(p, op)] -> [(p, op)]
//                | [] -> []
//            eliminateNearbyDuplicate (List.sortBy (fun (_, op) -> op) l)
//        nl <- duplicateElimination nl
//        
//        rules <- Map.add (q, m, gamma) nl rules
//    
//    Map.iter iterFunc kptsa.delta
//    {
//        kptsa with
//            delta = rules
//    }

// a wrong version -- may lead to loop trace
//let epsilonElimination (kptsa : KPTSA) =
//    let rules = kptsa.delta
//    /// cancel q -> q to be Omega (or functionally can just cancel this rule)
//    /// replace q -> q', if no q', add Omega (or just cancel this rule)
//    /// should also eliminate duplicate
//    let rec genNewRules rules =
//        let mutable changed = false
//        let mutable retRules = Map.empty
//        let iterFunc (q, m, gamma) l : unit =
//            let mutable nl = []
//            List.iter
//                (fun (p, op) ->
//                match op with
//                | TransOp.TransState q' ->
//                    changed <- true
//                    if q = q' then ()
//                    else
//                        match Map.tryFind (q', m, gamma) rules with
//                        | None -> ()
//                        | Some tl ->
//                            List.iter
//                                (fun (p', op) ->
//                                nl <- (p * p', op) :: nl)
//                                tl
//                | _ -> nl <- (p, op) :: nl)
//                l
//            
//            // eliminate duplicate
//            let duplicateElimination (l : (NumericType * TransOp) list) =
//                let rec eliminateNearbyDuplicate l =
//                    match l with
//                    // has >= 2 elements
//                    | (p, op) :: (p', op') :: l' ->
//                        if op = op' then
//                            eliminateNearbyDuplicate ((p + p', op) :: l')
//                        else
//                            (p, op) :: eliminateNearbyDuplicate ((p', op') :: l')
//                    // has < 2 elements
//                    | [(p, op)] -> [(p, op)]
//                    | [] -> []
//                eliminateNearbyDuplicate (List.sortBy (fun (_, op) -> op) l)
//            nl <- duplicateElimination nl
//                    
//            retRules <- Map.add (q, m, gamma) nl retRules
//        
//        Map.iter iterFunc rules
//        (retRules, changed)
//    let mutable changed = false
//    let mutable retRules = rules
//    
//    let (tmpRule, tmpChanged) = genNewRules rules
//    retRules <- tmpRule
//    changed <- tmpChanged
//    while changed do
//        let (tmpRule, tmpChanged) = genNewRules retRules
//        retRules <- tmpRule
//        changed <- tmpChanged
//    
//    {
//        kptsa with
//            delta = retRules
//    }

type ExprSystem = (int * Expr) list

exception BreakMarkException

/// this function is a very easy version of solving, in that it could not deal with infinitely many answers
/// if the system can be solved, it returns the list of value of each variable, if it cannot, returns just None
///
/// Currently, this function can only solve expr system of form: c + \sum_i c_i * v_i
let solveExpectedTerminationTimeExprSystem (es : ExprSystem) =
    let es = Array.ofList (fst (reindexedExprSystem es))
    let dimension = es.Length
    let matrix =
        let mapFunc (vId, expr) =
            // D + 1 because there is a constant dimension
            let retArr = Array.create (dimension + 1) NUMERIC_ZERO
            let rec analyseExpr e =
                match e with
                | EAdd (e1, e2) ->
                    analyseExpr e1
                    analyseExpr e2
                | EMul (EConst c, EVar i) ->
                    retArr.[i] <- retArr.[i] + c
                | EMul (EVar i, EConst c) ->
                    retArr.[i] <- retArr.[i] + c
                | EVar i ->
                    retArr.[i] <- retArr.[i] + 1
                // on the RHS, so minus it
                | EConst c -> retArr.[dimension] <- (NUMERIC_ZERO - c)
                | _ ->
                    failwith
                        "Invalid Input, only accepts expr system whose expressions are of form: c + \sum_i c_i * v_i."
            analyseExpr expr
            // move RHS single variable onto LHS
            retArr.[vId] <- retArr.[vId] - NUMERIC_ONE
            retArr
        Array.map mapFunc (Array.indexed es)
    try
        // steps forward
        for i in 0 .. dimension - 1 do
            if matrix.[i].[i] = NUMERIC_ZERO then
                try
                    for j in i + 1 .. dimension - 1 do
                        if matrix.[j].[i] <> NUMERIC_ZERO then
                            let tmp = matrix.[i]
                            matrix.[i] <- matrix.[j]
                            matrix.[j] <- tmp
                            raise BreakMarkException
                    // this means it has either infinite solutions or no solutions, but the former is not possible so it
                    // should be treated as having no solution, raise this mark for outside to catch and return None
                    raise (NFMarkException x0New)
                with
                | BreakMarkException -> ()
            // here, matrix.[i].[i] should be non-0
            for j in i + 1 .. dimension - 1 do
                let c = matrix.[j].[i] / matrix.[i].[i]
                if c <> NUMERIC_ZERO then
                    matrix.[j].[i] <- NUMERIC_ZERO
                    for k in i + 1 .. dimension do
                        matrix.[j].[k] <- matrix.[j].[k] - c * matrix.[i].[k]
        // steps backward
        let resArr = Array.map (fun arr -> Array.get arr dimension) matrix
        for i = dimension - 1 downto 0 do
            resArr.[i] <- resArr.[i] / matrix.[i].[i]
            for j = i - 1 downto 0 do
                // we should treat the current matrix.[i].[i] as 1
                resArr.[j] <- resArr.[j] - matrix.[j].[i] * resArr.[i]
        // return value
        Some resArr
    with
    | NFMarkException _ -> None

type PAHORSType =
    | RSTAny  // a place holder
    | RSTBase
    | RSTProd of PAHORSType array
    | RSTApp of PAHORSType array
    
    /// convert to the form that:
    /// 1. product type cannot have product type as its internal type -- smooth all product type
    /// 2. the last element of app type cannot be app type
    static member ToCanonicalForm (ty : PAHORSType) =
        match ty with
        | RSTAny -> RSTAny
        | RSTBase -> RSTBase
        | RSTProd pl ->
            if pl.Length = 1 then Array.exactlyOne pl
            elif pl.Length > 1 then
                let tpl =
                    Array.fold
                        (fun rl ty ->
                            match PAHORSType.ToCanonicalForm ty with
                            | RSTProd pl -> Array.append rl pl
                            | _ -> Array.append rl [|ty|])
                        [||]
                        pl
                RSTProd tpl
            else failwith "Invalid Type -- empty Prod list."
        | RSTApp al ->
            if al.Length = 1 then Array.exactlyOne al
            elif al.Length > 1 then
                let nal = Array.map PAHORSType.ToCanonicalForm al
                match nal.[nal.Length - 1] with
                | RSTApp al ->
                    RSTApp (Array.append (Array.sub nal 0 (nal.Length - 1)) al)
                | _ -> RSTApp nal
            else failwith "Invalid Type -- empty App list."

type PAHORSSymbol<'nt, 'var> =
    /// RSST: Recursion Schemes Symbol Type
    | RSSTTerminate
    | RSSTDiv
    | RSSTVariable of 'var
    | RSSTNonTerminal of 'nt

type PAHORSTerm<'st> =
    | RSTTApp of 'st * PAHORSTerm<'st> array
    | RSTTProd of PAHORSTerm<'st> array
    | RSTTProj of int * PAHORSTerm<'st>

type PAHORS =
    {
        nonTerminals : PAHORSType array
        /// array index: NonTerminal index, in order to have a quick random access
        /// number of arguments can be found in the nonTerminals field
        rules : (NumericType * PAHORSTerm<PAHORSSymbol<int, int>>) array array
        /// for automatically generated non-terminals, do not count their first Up as step
        /// to maintain exact step count value, if the ntNo is larger than this bound, they're not counted
        nonCountNonTerminalsBound : int
        /// this field gives the actual parameter amount for rules for each non-terminal
        nonTerminalActualPara : int array array
        /// the first rule is S
        nonTerminalPrintTable : string array
        variablePrintTable : string array array array
        /// if this exists, only count those rules that within this count rules
        /// (upNtNo, upRuleNo) |-> count / not count
        countRules : HashSet<int * int> option
    }

let printNonTerminal grammar ntNo =
    if grammar.nonTerminals.Length <= ntNo then
        failwith $"Cannot print Non Terminal No. {ntNo}, for it exceeds the maximum range."
//    match grammar.nonTerminalPrintTable with
//    | None ->
//        if ntNo = 0 then
//            "S"
//        else $"F{ntNo}"
//    | Some table ->
//        table.[ntNo]
    grammar.nonTerminalPrintTable.[ntNo]

let printVariable grammar (ntNo, rNo) vNo =
    if grammar.nonTerminals.Length <= ntNo then
        failwith "No such non terminal"
//    match grammar.variablePrintTable with
//    | None ->
//        $"x{ntNo}@{printNonTerminal grammar ntNo}"
//    | Some table ->
//        table.[ntNo].[rNo].[vNo]
    grammar.nonTerminalPrintTable.[ntNo]
        
let printSymbol grammar (ntNo, rNo) symbol =
    if grammar.nonTerminals.Length <= ntNo then
        failwith "No such non terminal"
    match symbol with
    | RSSTVariable argNo -> printVariable grammar (ntNo, rNo) argNo
    | RSSTDiv -> "Omega"
    | RSSTTerminate -> "tt"
    | RSSTNonTerminal ntNo -> printNonTerminal grammar ntNo
    
let rec printTerm grammar (ntNo, rNo) term : string =
    if grammar.nonTerminals.Length <= ntNo then
        failwith "No such non terminal"
    let printSym = printSymbol grammar (ntNo, rNo)
    // when calling recall, parentheses will be added to multiple application terms
    let recall t =
        match t with
        | RSTTApp (sym, l) ->
            if l.Length = 0 then
                printSym sym
            else "(" + (printTerm grammar (ntNo, rNo) t) + ")"
        | RSTTProj _ ->
            "(" + printTerm grammar (ntNo, rNo) t + ")"
        | _ -> printTerm grammar (ntNo, rNo) t
    match term with
    | RSTTApp (sym, al) ->
        let mutable ret = (printSym sym)
        Array.iter
            (fun t ->
            ret <- ret + " " + recall t)
            al
        ret
    | RSTTProd pl ->
        let mutable ret = "<"
        for i, t in Array.indexed pl do
            ret <- ret + (if i = 0 then "" else ", ") + printTerm grammar (ntNo, rNo) t
        ret + ">"
    | RSTTProj (q, t) ->
        $"\\pi{{{q + 1}}} " + recall t

/// checked
let printRule grammar (ntNo, rNo) =
    // F
    let mutable ret = printNonTerminal grammar ntNo
    // F \tilde{x}
    match grammar.nonTerminals.[ntNo] with
    | RSTApp _ ->
        for argNo in 0 .. grammar.nonTerminalActualPara.[ntNo].[rNo] - 1 do
            ret <- ret + " " + printVariable grammar (ntNo, rNo) argNo
    | _ -> ()
    // F \tilde{x} =(p)=
    let p, t = grammar.rules.[ntNo].[rNo]
    ret <- ret + $" =({p})= "
    // F \tilde{x} =(p)= t
    ret + printTerm grammar (ntNo, rNo) t

let checkLinearity grammar (ntNo, rNo) t =
    let unionUsedMap (o : bool array) (n : bool array) =
        let mutable ret = Array.create o.Length false
        for i in 0 .. o.Length - 1 do
            ret.[i] <- o.[i] && n.[i]
        ret
    let rec checkLinearityOfTerm t (usedMap : bool array) =
        match t with
        | RSTTApp (sym, al) ->
            let mutable newUsedMap = usedMap.Clone () :?> bool []
            match sym with
            | RSSTVariable vNo ->
                if usedMap.[vNo] then
                    let s =
                        $"In rule \"{printRule grammar (ntNo, rNo)}\", variable \"{printVariable grammar (ntNo, rNo) vNo}" +
                            "\" used for more than 1 time."
                    failwith s
                newUsedMap.[vNo] <- true
            | _ -> ()
            Array.iter
                (fun t ->
                    let um = checkLinearityOfTerm t newUsedMap
                    newUsedMap <- unionUsedMap newUsedMap um)
                al
            newUsedMap
        | RSTTProd pl ->
            let mutable newUsedMap = usedMap
            Array.iter
                (fun t ->
                    let um = checkLinearityOfTerm t usedMap
                    newUsedMap <- unionUsedMap newUsedMap um)
                pl
            newUsedMap
        | RSTTProj (_, t) -> checkLinearityOfTerm t usedMap
    checkLinearityOfTerm t (Array.create grammar.nonTerminalActualPara.[ntNo].[rNo] false) |> ignore

/// checked
let rec printType ty =
    let printSequentType (l : PAHORSType array) connector printer =
        let mutable ret = ""
        for i in 0 .. l.Length - 1 do
            if i > 0 then ret <- ret + connector
            ret <- ret + printer l.[i]
        ret
    let recall ty =
        match ty with
        | RSTApp _ -> $"({printType ty})"
        | _ -> printType ty
    match ty with
    | RSTAny -> "T"
    | RSTApp al ->
        printSequentType
            al
            (" " + Flags.LINEAR_MAP_SYMBOL + " ")
            recall
    | RSTBase -> "o"
    | RSTProd pl ->
        printSequentType pl " & " recall

/// checked
// any is not allowed when a type is actually required
let pahorsValidityChecking (grammar : PAHORS) =
    if grammar.nonTerminals.[0] <> RSTBase then
        failwith "The start symbol must be of type 'o'"
    if grammar.nonTerminals.Length <> grammar.rules.Length then
        failwith "Some non-terminals undefined, either rule body or type."
    // check probability
    begin
        Array.iter
            (fun (ntNo, lst) ->
                let prob = Array.sumBy fst lst
                if (NUMERIC_ONE < prob) || (prob < NUMERIC_ZERO) then
                    failwith
                        $"Invalid Production, the probability of non-terminal {printNonTerminal grammar ntNo} is {prob}"
                if prob = NUMERIC_ZERO then
                    printfn $"Warning: the probability of non-terminal {printNonTerminal grammar ntNo} is 0.")
            (Array.indexed grammar.rules)
    end
    // check linearity / affineness
    begin
        Array.iter
            (fun (ntNo, lst) ->
                Array.iter (fun (rNo, (_, t)) -> checkLinearity grammar (ntNo, rNo) t) (Array.indexed lst))
            (Array.indexed grammar.rules)
    end
    let mutable nonTerminalNo = 0
    let mutable ruleNo = 0
    
    // a supporting function to throw exceptions
    let fail subTerm msg =
        printfn "Type Checking Fail with:"
        printfn $"In the rule for non-terminal {printNonTerminal grammar nonTerminalNo}: "
        printfn $"{printRule grammar (nonTerminalNo, ruleNo)}"
        match subTerm with
        | None -> ()
        | Some t -> printfn $"In sub-term: {printTerm grammar (nonTerminalNo, ruleNo) t}"
        printfn $"Message: {msg}"
        failwith "Type Checking Fail."
    
    // get symbol type
    let symbolType (sym : PAHORSSymbol<int, int>) =
        match sym with
        | RSSTVariable argNo ->
            match grammar.nonTerminals.[nonTerminalNo] with
            | RSTApp al ->
                if al.Length <= argNo then
                    fail None "INTERNAL: No such argument."
                al.[argNo]
            | _ -> fail None "INTERNAL: No such argument."
        | RSSTNonTerminal ntNo ->
            if grammar.nonTerminals.Length <= ntNo then
                fail None "INTERNAL: No such non-terminal."
            grammar.nonTerminals.[ntNo]
        | _ -> RSTBase
    
    // to get the type of a term, when not typable, an exception is thrown
    // nonTerminalNo is for argument type acquisition
    let rec termType (term : PAHORSTerm<PAHORSSymbol<int, int>>) =
        let fail msg = fail (Some term) msg
        match term with
        | RSTTProd cl ->
            RSTProd (Array.map termType cl)
        | RSTTProj (q, t) ->
            let ty = termType t
            match ty with
            | RSTProd pl ->
                if q >= pl.Length then
                    fail $"Projection range exceeded, the product type only has length {pl.Length}"
                pl.[q]
            | _ ->
                fail $"The target of projection should be product type, while has type: {printType ty}"
        | RSTTApp (sym, al) ->
            let ht = symbolType sym
            if al.Length = 0 then
                ht
            else
                match ht with
                | RSTApp pl ->
                    if pl.Length <= al.Length then
                        fail ("The length of argument list exceeds parameter list's, " +
                              $"{printSymbol grammar (nonTerminalNo, ruleNo) sym} expect to " +
                              $"have at most {pl.Length - 1} " +
                              $"parameters, while given {al.Length}")
                    for i in 0 .. al.Length - 1 do
                        let at = termType al.[i]
                        if pl.[i] <> at then
                            fail ($"The {i + 1} argument \"{printTerm grammar (nonTerminalNo, ruleNo) al.[i]}\" " +
                                  $"has type {printType at}, " +
                                  $"which is supposed to have type {printType pl.[i]}")
                    if pl.Length - al.Length = 1 then
                        Array.last pl
                    else
                        RSTApp pl.[al.Length ..]
                | _ ->
                    fail $"This head type must be of application form, while has type: {printType ht}"
    
    for ntNo in 0 .. grammar.rules.Length - 1 do
        let ntRuleList = grammar.rules.[ntNo]
        nonTerminalNo <- ntNo
        for rNo in 0 .. ntRuleList.Length - 1 do
            ruleNo <- rNo
            let expectedType =
                let paras = grammar.nonTerminalActualPara.[ntNo].[rNo]
                if paras = 0 then grammar.nonTerminals.[ntNo]
                else
                    match grammar.nonTerminals.[ntNo] with
                    | RSTApp al ->
                        if al.Length <= paras then
                            fail None "Too many parameters."
                        let nal = Array.sub al paras (al.Length - paras)
                        if nal.Length = 1 then nal.[0] else RSTApp nal
                    | _ -> fail None "This non-terminal cannot have parameter."
            let ruleBody = snd ntRuleList.[rNo]
            let actualType = termType ruleBody
            if actualType <> expectedType then
                fail None
                    ("The body of the rule is expected to have type:" +
                     printType expectedType + ", " +
                     "while has type: " + printType actualType)
    
    true

// Not a good algorithm -- this may cause k explosion -- (|Gamma| + 1)k
///// A variant of algorithm by Denkinger, it outputs an equivalent loop-free k-PTSA
///// with the same Step Count and the same 
//let epsilonTransformation (kptsa : KPTSA) =
//    if KPTSA.EpsilonLoopDetect kptsa then
//        let newStateTable = IndexingTable.CreateIndexingTableWithInitIndex<TransOp> (kptsa.maxState + 1)
//        let newGammaTable = IndexingTable.CreateIndexingTableWithInitIndex<LocalMemory * Gamma> (kptsa.maxGamma + 1)
//        let newStepCounts =
//            match kptsa.stepCount with
//            | Some sc -> sc
//            | None ->
//                Map.fold
//                    (fun rm (q, m, gamma) ->
//                        List.fold
//                            (fun rm (_, op) ->
//                                match op with
//                                // epsilon translation should be treated separately
//                                | TransState _ -> rm
//                                | _ -> Map.add (q, m, gamma, op) (uint64 1) rm)
//                            rm)
//                    Map.empty
//                    kptsa.delta
//        let newRules, newStepCounts =
//            let foldFunc (nRules, nStepCounts) (q, m, gamma) pOpLst =
//                let normalOpLst, epsilonOpLst =
//                    let findEpsilonFoldFuc (normalOpLst, epsilonOpLst) (p, op) =
//                        match op with
//                        | TransState _ -> normalOpLst, (p, op) :: epsilonOpLst
//                        | _ -> (p, op) :: normalOpLst, epsilonOpLst
//                    List.fold findEpsilonFoldFuc ([], []) pOpLst
//                if List.isEmpty epsilonOpLst then
//                    Map.add (q, m, gamma) pOpLst nRules, nStepCounts
//                else
//                    let proxyLMGamma = newGammaTable.lookUp (m, gamma)
//                    // nRules should add:
//                    // current config |-> normal Op list + going up to proxyLMGamma with epsilon Op list
//                    // normal Op q with current m, gamma |-> conduct Op right away
//                    // current q with m0, proxyGamma |-> all epsilon Op list + normal Op Down
//                    // normal Op Down with m0, proxyGamma |-> continue Down
//                    failwith "
//            Map.fold foldFunc (Map.empty, newStepCounts) kptsa.delta
//        failwith 
//    else
//        kptsa

let lispPrintProbability (c : NumericType) = c.printInNlSatForm ()

let rec lispPrintExpr (e : Expr) : string =
    match e with
    | EAdd (e1, e2) ->
        $"(+ {lispPrintExpr e1} {lispPrintExpr e2})"
    | EMinus (e1, e2) ->
        $"(- {lispPrintExpr e1} {lispPrintExpr e2})"
    | EMul (e1, e2) ->
        $"(* {lispPrintExpr e1} {lispPrintExpr e2})"
    | EDiv (e1, e2) ->
        $"(/ {lispPrintExpr e1} {lispPrintExpr e2})"
    | EConst c -> lispPrintProbability c
    | EVar v -> printExprVariable v
    
let nlSatVarDecl var = $"(declare-const {var} Real)"
let nlSatAssertExpr (lispExpr : string) =
    if String.IsNullOrEmpty lispExpr then "(assert True)" else
    $"""(assert {if lispExpr[0] = '(' then lispExpr else $"({lispExpr})"})"""

let genNLSatDeclarePart es declare1Bound =
    let mutable ret = ""
    List.iter
        (fun (i, _) ->
            ret <- ret + $"(declare-const {printExprVariable i} Real)\n"
            ret <- ret + $"(assert (>= {printExprVariable i} 0.0))"
            if declare1Bound then
                ret <- ret + $"(assert (<= {printExprVariable i} 1.0))")
        es
    ret

let genNLSatEsDefPart es =
    List.fold
        (fun ret (i, e) ->
            ret + $"(assert (= {printExprVariable i} {lispPrintExpr e}))\n")
        ""
        es

let NLSatTriggerString = "(check-sat)"

let genNLSatQueryString (es : ExprSystem) newQueryStatement : string =
    genNLSatDeclarePart es true + genNLSatEsDefPart es + $"(assert {newQueryStatement})\n" + NLSatTriggerString

let printPAHORS pahors =
    flip Array.map (Array.indexed pahors.rules) (fun (ntNo, arr) ->
        flip Array.map (Array.indexed arr) $ fun (rNo, _) ->
            printRule pahors (ntNo, rNo) + "\n")
    |> Array.concat
    |> Array.reduce (+)

/// returns the A matrix, the B vector, the map of variable index to matrix dimension
let linearEquationSystemToMatrixVec es =
    // mapping the variable to the matrix dimension
    let matMap =
        Seq.map fst es
        |> Seq.indexed
        |> Seq.map swap
        |> HashMap.fromSeq in
    let LEN = Seq.length es in
    flip Seq.map es (fun (v, e : Expr) ->
        let arr = Array.init LEN $ fun _ -> NUMERIC_ZERO in
        let mutable cst = NUMERIC_ZERO in
        let (NormalisedExpr e) = normaliseExprEnv $ toExprEnv e in
        flip List.iter e (fun (NormalisedExprAtom (c, vs)) ->
            match vs with
            | []  -> cst <- cst - c
            | [v] -> arr[matMap[v]] <- arr[matMap[v]] + c
            | _   -> failwith "The given equation system is not linear.");
        arr[matMap[v]] <- arr[matMap[v]] - NUMERIC_ONE;
        (arr, cst))
    |> Seq.toArray
    |> Array.unzip
    |> fun (mat, arr) -> mat, arr, matMap

/// iterate the given equation system by PReMo
let iterByPReMo (eqSys : #seq<int * Expr>) =
    printfn "Calling PReMo..."
    let writeEquation vId expr =
        let expr = normaliseExpr expr in
        let eStr = expr.ToString ((fun id -> $"x{id}"), fun x -> toString $ x.getDouble ()) in
        $"x{vId} = {eStr}" in
    let eqStr =
        Seq.map (uncurry writeEquation) eqSys
        |> String.concat "\n" in
    let premoResult =
        callPremoEquationEngine Flags.PREMO_JAR_PATH eqStr Flags.PREMO_ADDITIONAL_ARGUMENTS in
    match premoResult with
    | Ok retLines ->
        if Flags.INNER_DEBUG then println $ String.concat "\n" retLines;
        List.tail retLines
        |> List.map (fun x ->
            match x.Split "=" with
            | [| varName; res |] ->
                // the first symbol is always "x"
                let vId = varName[1..] in
                (Int32.Parse vId, NumericType.Parse res)
            | _ -> failwith $"Invalid return result from PReMo, returned line: \"{x}\"")
        |> fun res ->
            if Flags.DEBUG then begin
                let res = List.map (BiMap.fstMap (fun x -> $"x{x}")) res in
                printfn $"PReMo result: {res}"
            end;
            res
    | Error errMsg ->
        failwith $"PReMo error:\n{errMsg}"
