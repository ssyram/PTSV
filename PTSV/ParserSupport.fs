module PTSV.ParserSupport

open System.Collections.Generic
open Microsoft.FSharp.Collections
open PTSV.Core
open PTSV.Global
open PTSV.NewEquationBuild
open PTSV.Utils
open PTSV.ProbabilisticPushDownAutomaton

let DUMMY_PBPA_TO_PPDA_STATE = "$"

let parseArithOp =
    function
    | "+" -> (+)
    | "-" -> (-)
    | "*" -> (*)
    | "/" -> (/)
    | op  -> failwith $"not support arithmetic operator \"{op}\""
    
type ParseExpr =
    | PEVar of string
    | PEConst of NumericType
    | PEOp of opName:string * ParseExpr list
    member x.eval map =
        match x with
        | PEVar v ->
            begin match Map.tryFind v map with
            | Some res -> res
            | None -> failwith $"name \"{v}\" not defined."
            end
        | PEConst c -> c
        | PEOp (op, exprList) ->
            List.reduce (parseArithOp op) $ flip List.map exprList (fun x -> x.eval map)
    override x.ToString () =
        match x with
        | PEVar var -> $"{var}"
        | PEConst c -> $"{c}"
        | PEOp (op, [e1; e2]) ->
            let modify e =
                match e with
                | PEOp ("+", _) | PEOp ("-", _) -> $"({e})"
                | _                             -> $"{e}" in
            match op with
            | "+" -> $"{e1} + {e2}"
            | "-" ->
                match e2 with
                | PEOp ("+", _) | PEOp ("-", _) -> $"{e1} - ({e2})"
                | _ -> $"{e1} - {e2}"
            | "*" ->
                $"{modify e1} * {modify e2}"
            | "/" ->
                match e2 with
                | PEVar _ | PEConst _ -> $"{modify e1} / {e2}"
                | _                   -> $"{modify e1} / ({e2})"
            | _ -> IMPOSSIBLE ()
        | _ -> IMPOSSIBLE ()
                
                
    
// ------------------------------- PAHORS -------------------------------

//type ParseType =
//    | TBase
//    | TApp of ParseType * ParseType
//    | TProd of ParseType list
//    member x.toPAHORSType () =
//        match x with
//        | TBase -> RSTBase
//        | TApp (arg, ret) ->
//            let arg = arg.toPAHORSType () in
//            match ret.toPAHORSType () with
//            | RSTApp args -> RSTApp $ Array.append [| arg |] args
//            | ret         -> RSTApp [| arg; ret |]
//        | TProd prods ->
//            flip List.map prods (fun x -> x.toPAHORSType ())
//            |> Array.ofList
//            |> RSTProd
type ParseTerm =
    | PTIdent of string
    | PTApp of ParseTerm * ParseTerm
    | PTProd of ParseTerm list
    | PTProj of int * ParseTerm
    override x.ToString () =
        match x with
        | PTIdent name -> name
        | PTApp (t1, t2) ->
            match t2 with
            | PTIdent _ | PTProd _ -> $"{t1} {t2}"
            | _                    -> $"{t1} ({t2})"
        | PTProd ts ->
            printFullSeq_full (fun x -> $"{x}") "<" ">" ", " ts
        | PTProj (idx, t) ->
            match t with
            | PTIdent _ | PTProd _ -> $"\\pi({idx}) {t}"
            | _                    -> $"\\pi({idx}) ({t})"
    member x.toPAHORSTerm ntMap paraMap : PAHORSTerm<PAHORSSymbol<int, int>> =
        match x with
        | PTIdent "\\top" -> RSTTApp (RSSTTerminate, [||])
        | PTIdent "\\Omega" -> RSTTApp (RSSTDiv, [||])
        | PTIdent name ->
            match name.ToLower () with
            | "\\top" -> RSTTApp (RSSTTerminate, [||])
            | "\\omega" -> RSTTApp (RSSTDiv, [||])
            | _ -> begin  // debug -- do not rebind name, as this is used for non-terminal
                match Map.tryFind name paraMap with
                | Some vIdx -> RSTTApp (RSSTVariable vIdx, [||])
                | None -> match Map.tryFind name ntMap with
                          | None ->
                              let word =
                                  $"Unknown PAHORS symbol \"{name}\", guess it's an "
                                  + "undeclared and undefined non-terminal. "
                                  + "Hint: the termination symbol is \\top "
                                  + "and the explicit divergence symbol is \\Omega."
                              in
                              failwith word
                          | Some ntIdx -> RSTTApp (RSSTNonTerminal ntIdx, [||])
            end
        | PTApp (t1, t2) ->
            match t1.toPAHORSTerm ntMap paraMap with
            | RSTTApp (hdSym, arr) -> RSTTApp (hdSym, Array.append arr [|t2.toPAHORSTerm ntMap paraMap|])
            | _ ->
                let word =
                    "Currently support ONLY head-normal application -- "
                    + "projections should be written separately, for example: "
                    + "for \"\\pi(1) x t1 t2\", one should write a non-terminal, say, \"F\" with "
                    + "definition \"F x := \\pi(1) x\" and write \"F x t1 t2\" instead."
                in 
                failwith word
        | PTProd lst ->
            flip List.map lst (fun x -> x.toPAHORSTerm ntMap paraMap)
            |> Array.ofList
            |> RSTTProd
        | PTProj (dim, t) -> RSTTProj (dim, t.toPAHORSTerm ntMap paraMap)
type ParsePAHORSRule =
    | ParsePAHORSRule of
        nt:string *
        paraList:string list *
        prob:ParseExpr *
        body:ParseTerm
    member x.toPAHORSRule ntMap macroDef =
        let (ParsePAHORSRule (nt, paraList, prob, body)) = x in
        match Map.tryFind nt ntMap with
        | None -> failwith $"Undeclared non-terminal \"{nt}\", type unknown."
        | Some ntIdx ->
            let paraMap = List.indexed paraList
                          |> List.map swap
                          |> Map.ofList in
            (ntIdx, paraList, prob.eval macroDef, body.toPAHORSTerm ntMap paraMap)
    override x.ToString () =
        match x with
        | ParsePAHORSRule (nt, paras, prob, body) ->
            let probStr =
                if prob = PEConst NUMERIC_ONE then "" else $"({prob})" in
            $"""{nt} {printFullSeq_full toString "" "" " " paras} {probStr}-> {body}"""
    
// ------------------------------ PAHORS Types --------------------------
type ParseType =
    | PTyBase
    | PTyImpl of ParseType * ParseType
    | PTyProd of ParseType list
    override x.ToString () =
        match x with
        | PTyBase -> "o"
        | PTyImpl (ty1, ty2) ->
            let sTy1 =
                match ty1 with
                | PTyImpl _ -> $"({ty1})"
                | _         -> $"{ty1}" in
            $"{sTy1} -> {ty2}"
        | PTyProd tys ->
            match List.length tys with
            | 0 -> IMPOSSIBLE ()
            | 1 -> $"{List.exactlyOne tys}"
            | _ ->
                let printer ty =
                    match ty with
                    | PTyBase -> $"{ty}"
                    | _       -> $"({ty})" in
                List.map printer tys
                |> String.concat " & "
let prodMap f = function PTyProd types -> PTyProd $ f types | _ -> IMPOSSIBLE ()
let unitUnwrap = function PTyProd [x] -> x | x -> x
let rec collectApp =
    function PTyImpl (t1, t2) -> t1 :: collectApp t2 | x -> [x]
let rec parseTypeToRealType ty =
    match ty with
    | PTyBase -> RSTBase
    | PTyProd lst -> RSTProd $ Array.ofList (List.map parseTypeToRealType lst)
    | PTyImpl (t1, t2) ->
        RSTApp $ Array.ofList (List.map parseTypeToRealType $ t1 :: collectApp t2)
    
// ---------------------------- PAHORS Types End -------------------------
type TypeDeclPair =
    | TypeDeclPair of string * ParseType
    override x.ToString () =
        match x with
        | TypeDeclPair (nt, ty) -> $"{nt} : {ty}"
        

exception private TypingException of pos:ParseTerm list * msg:string

let rec private typing tyEnv term =
    let recall t = try typing tyEnv t
                   with
                   | TypingException (pos, msg) -> raise $ TypingException (term :: pos, msg) in 
    match term with
    | PTIdent name ->
        match name.ToLower () with
        | "\\top" | "\\omega" -> PTyBase
        | _ -> Map.find name tyEnv
    | PTApp (t1, t2) ->
        let ty1 = recall t1 in
        let ty2 = recall t2 in
        match ty1 with
        | PTyImpl (arg, ret) ->
            if arg <> ty2 then
                raise $ TypingException (
                    [term],
                    $"Term \"{t2}\" is expected to have type \"{arg}\" but is having type \"{ty2}\"");
            ret
        | _ ->
            raise $ TypingException (
                [term],
                $"Term \"{t1}\" is expected to have function type, but is having type \"{ty1}\"")
    | PTProd ts -> PTyProd $ List.map recall ts
    | PTProj (idx, t) ->
        match recall t with
        | PTyProd tys ->
            if List.length tys < idx then
                raise $ TypingException (
                    [term],
                    $"Term \"{t}\" has product type less than the specified projection.");
            tys[idx]
        | ty ->
            let word =
                $"Term \"{t}\" is expected to have product type of length at least {idx + 1}, " +
                $"but is having type {ty}."
            in
            raise $ TypingException (
                [term],
                word)
    
type TermNormaliseResult = (ParsePAHORSRule * ParseType) list * ParseTerm

let rec private appNTimes n ty =
    if n <= 0 then ty
    else
        match ty with
        | PTyImpl (_, ret) -> appNTimes (n - 1) ret
        | _                -> failwith $"Trying to get return type from \"{ty}\"."

let private typeCheckParseRule ntEnv (ParsePAHORSRule (nt, paras, _, term) as rule) =
    let ntTy =
        match Map.tryFind nt ntEnv with
        | Some ty -> ty
        | None    -> failwith $"Non-terminal \"{nt}\" undeclared." in
    let ntApps = collectApp ntTy in
    if List.length ntApps <= List.length paras then
        let word =
            $"Non-terminal \"{nt}\" is expected to have at most \"{List.length ntApps - 1}\" parameters, " +
            $"while in definition \"{rule}\", there are \"{List.length paras}\""
        in
        failwith word;
    let tyEnv : Map<string,ParseType> =
        listSafeZip paras ntApps
        |> List.fold (flip (uncurry Map.add)) ntEnv
    in
    let expTy = appNTimes (List.length paras) ntTy in
    try
        let realTy = typing tyEnv term in
        if realTy <> expTy then
            let word =
                $"In rule \"{rule}\", the term body is expected to have type \"{expTy}\" " +
                $"but is having type \"{realTy}\"."
            in
            failwith word
    with
    | TypingException (pos, msg) ->
        let word =
            $"In rule \"{rule}\", " +
            String.concat "" (List.map (fun x -> $"in Term \"{x}\", ") pos) +
            msg
        in
        failwith word
            
/// make \pi(i) ... be an application new term and generate the new non-terminal
/// getNextNewName : to make a new unique name for the new terminal
///
/// for example:
///     \pi(1) t1 t2
/// =>
///     $Pi(F)@0%1 t1 t2
/// &
///     $Pi(F)@0%1 : Type(t1) -> Type(\pi(1) t1)
///     $Pi(F)@0%1 x -> \pi(1) x
let rec private normaliseTerm getNextNewName tyEnv term =
    let recall term = normaliseTerm getNextNewName tyEnv term in
    match term with
    | PTIdent _ -> ([], term)
    | PTApp (t1, t2) ->
        let l1, t1 = recall t1 in
        let l2, t2 = recall t2 in
        (l1 ++ l2, PTApp (t1, t2))
    | PTProd ts ->
        List.map recall ts
        |> List.unzip
        |> BiMap.pairMap (List.concat, PTProd)
    | PTProj (idx, t) ->
        let ntName = getNextNewName () in
        let rule = ParsePAHORSRule (ntName, ["x"], PEConst NUMERIC_ONE, PTProj (idx, PTIdent "x")) in
        let retTy = typing tyEnv term in
        let argTy = typing tyEnv t in
        let ty = PTyImpl (argTy, retTy) in
        let l, t = recall t in
        (TypeDeclPair (ntName, ty), rule) :: l, PTApp (PTIdent ntName, t)
    
/// must ensure the validity of the given Model -- especially passing type check.
let private normalisePAHORSModel tyDecl rules =
    let ntEnv : Map<string,ParseType> =
        List.map (fun (TypeDeclPair (x, y)) -> (x, y)) tyDecl
        |> Map.ofList in
    // for each rule, map to the normalised rule and the newly generated projections
    let mapper rId (ParsePAHORSRule (nt, paras, prob, term)) =
        let tyEnv =
            let ntApps = Map.find nt ntEnv |> collectApp in
            listSafeZip paras ntApps
            |> List.fold (flip (uncurry Map.add)) ntEnv
        in
        let mutable nextIdx = 0 in
        let genNewName () =
            let ret = $"$Pi({nt}@{rId}%%{nextIdx})" in
            nextIdx <- nextIdx + 1;
            ret
        in
        let newDefs, normTerm = normaliseTerm genNewName tyEnv term in
        let newRule = ParsePAHORSRule (nt, paras, prob, normTerm) in
        List.unzip newDefs
        |> BiMap.sndMap (List.append [newRule])
    in
    List.mapi mapper rules
    |> List.unzip
    |> BiMap.pairMap (List.concat, List.concat)
    |> BiMap.fstMap (List.append tyDecl)


//exception private UnionInfTypeException of name:string * ParseType * ParseType
///// the place and reason
//exception private ParseTermTypeCheckException of pos:ParseTerm list * msg:string

//let private unionInfTyRes res1 res2 =
//    // check
//    Map.toSeq res1
//    |> Seq.iter (fun (name, ty) ->
//        match Map.tryFind name res2 with
//        | Some ty' ->
//            if not (ty = ty') then
//                raise $ UnionInfTypeException (name, ty, ty')
//        | None -> ())
//    // union
//    Map.toSeq res1
//    |> Seq.append (Map.toSeq res2)
//    |> Map.ofSeq

/// may throw `ParseTermTypeCheckException` if the inference cannot be done.
//let rec private limitedTypeInfer tyEnv term infTy expTy =
//    let recall term expTy =
//        try
//            limitedTypeInfer tyEnv term infTy expTy
//        with
//        | ParseTermTypeCheckException (pos, msg) ->
//            // attach this term in the path
//            raise $ ParseTermTypeCheckException (term :: pos, msg)
//    in
//    match term with
//    | PTIdent name ->
//        if Set.contains name infTy then
//            match expTy with
//            | Some ty -> (expTy, Map.add name ty Map.empty)
//            | None    -> (expTy, Map.empty)
//        else
//            match Map.tryFind name tyEnv with
//            | Some ty -> begin
//                match expTy with
//                | Some expTy ->
//                    let word =
//                        $"Symbol \"{name}\" has type \"{ty}\" but it is used here as having type \"{expTy}\"."
//                    in
//                    if ty <> expTy then raise $ ParseTermTypeCheckException ([], word)
//                | None -> ()
//                (Some ty, Map.empty)
//                end
//            | None    ->
//                let word =
//                  $"Unknown PAHORS symbol \"{name}\", guess it's an "
//                  + "undeclared non-terminal. "
//                  + "Hint: the termination symbol is \\top "
//                  + "and the explicit divergence symbol is \\Omega."
//                in
//                failwith word
//    | PTApp (t1, t2) ->
//        let ty2, infRes2 = recall t2 None in
//        let ty1, infRes1 = recall t1 (PTyImpl ty2) in
//        match ty1 with
//        | PTyImpl (arg, ret) ->
//            let ty2, infRes2 = recall t2 arg in
//            // no need to check this, as every call should maintain this promise
//            if arg <> ty2 then
//                IMPOSSIBLE ()
//            // to maintain the promise
//            if ret <> expTy then
//                raise $ ParseTermTypeCheckException (
//                    [],
//                    $"Term \"{term}\" is expected to have type \"{expTy}\" but here has type \"{ret}\"")
//            let infRes =
//                try
//                    unionInfTyRes infRes1 infRes2
//                with
//                | UnionInfTypeException (name, ty1, ty2) ->
//                    let word =
//                        $"Symbol \"{name}\" has two simultaneous types \"{ty1}\" from \"{t1}\" " +
//                        $"and \"{ty2}\" from \"{t2}\"."
//                    in
//                    raise $ ParseTermTypeCheckException ([term], word)
//            in
//            (ret, infRes)
//        | _ ->
//            raise $ ParseTermTypeCheckException (
//                [term],
//                $"Term \"{t1}\" is expected to have function type, but here has type \"{ty1}\".")
//    | PTProd terms ->
//        match expTy with
//        | 


// ---------------------------------- rPTSA Start ---------------------------------- 
type RPTSAConfig =
    RPTSAConfig of
        k:int *
        q0:string *
        m0:string *
        gamma0:string
type RPTSARule =
    | RPTSARule of
        q:string *
        m:string *
        gamma:string *
        prob:ParseExpr *
        op:TransOp<string, string, string, TerOp>
    member x.toKPTSARule stateTable memoryTable gammaTable macroDefs =
        match x with
        | RPTSARule (q, m, g, pExpr, op) ->
            (IndexingTable.lookup stateTable q,
             IndexingTable.lookup memoryTable m,
             IndexingTable.lookup gammaTable g,
             pExpr.eval macroDefs,
             op.toKPTSATransOp
                (IndexingTable.lookup stateTable)
                (IndexingTable.lookup memoryTable)
                (IndexingTable.lookup gammaTable)
                (function | SpTer -> TransTer | SpDiv -> TransDiv))
        
let flattenProbStateList q m gamma lst =
    flip List.map lst $ fun (probExpr, q') ->
        RPTSARule (q, m, gamma, probExpr, OpTransState q')

// ---------------------------------- rPTSA End ----------------------------------

// ---------------------------------- pPDA Start ---------------------------------
type PPDAConfig<'st, 'g> =
    PPDAConfig of
        q0:'st *
        gamma0:'g
type PPDARule<'st, 'g> =
    PPDARule of
        q:'st *
        gamma:'g *
        prob:ParseExpr *
        rq:'st *
        rGammas:'g list
type PPDATransOp<'st, 'g> =
    | PPDATransState of q:'st
    | PPDATransPush of q:'st * gamma:'g
    | PPDATransPop of q:'st
let stdRuleToPPDARule q X prob op =
    match op with
    | PPDATransState q' -> PPDARule (q, X, prob, q', [X])
    | PPDATransPop q' -> PPDARule (q, X, prob, q', [])
    | PPDATransPush (q', Y) -> PPDARule (q, X, prob, q', [Y; X])
type StdPPDAState<'st, 'g> =
    | SPSOriginal of 'st
    | SPSRules of 'st * 'g list
/// the virtual bottom
let VIR_BOT = "$VB$"
/// the virtual start
let VIR_ST = "$VST$"
/// requires macroDefs to translate the probability value
/// requires gammaList to generate the first stuff
/// the final bool in the return list stands for whether this rule should be counted
let pPDARewritingRuleToStdRules macroDefs gammaList (PPDARule (q, X, prob, p, Xs)) =
    // reverse the list, as taking from head is more efficient
    let Xs = List.rev Xs in 
    let rec translateUpRules Xs curG =
        let q' = SPSRules (p, Xs) in
        match Xs with
        | [X] -> [(q', curG, NUMERIC_ONE, PPDATransPush (SPSOriginal p, X), false)]
        | X :: Xs ->
            (q', curG, NUMERIC_ONE, PPDATransPush $ (SPSRules (p, Xs), X), false) ::
            translateUpRules Xs X
        | [] -> IMPOSSIBLE ()
    in
    match Xs with
    | [Y] when X = Y ->
        [(SPSOriginal q, X, prob.eval macroDefs, PPDATransState $ SPSOriginal p, true)]
    | [Y; Z] when X = Y ->
        [(SPSOriginal q, X, prob.eval macroDefs, PPDATransPush (SPSOriginal p, Z), true)]
    | Y :: Z :: Xs when X = Y ->
        (SPSOriginal q, X, prob.eval macroDefs, PPDATransPush (SPSRules (p, Xs), Z), true) ::
        translateUpRules Xs Z
    | [] -> [(SPSOriginal q, X, prob.eval macroDefs, PPDATransPop $ SPSOriginal p, true)]
    | _ ->
        [(SPSOriginal q, X, prob.eval macroDefs, PPDATransPop $ SPSRules (p, Xs), true)] ++
        List.reduce (++) (List.map (translateUpRules Xs) gammaList)  
let private mentionedStates (PPDARule (q, _, _, rq, _)) = [ q; rq ]
let bottomProxyRules oriQ0 oriG0 (rules : PPDARule<_,_> list) =
    // VST VB -> qInit S VB  -- VST to avoid conflicting with states below
    // forall q. q VB -> q
    let allStates =
        List.collect mentionedStates rules
        |> Set.ofList
        |> Set.toList
    in
    let mapper q = PPDARule (q, VIR_BOT, PEConst NUMERIC_ONE, q, []) in
    PPDARule (VIR_ST, VIR_BOT, PEConst NUMERIC_ONE, oriQ0, [ oriG0; VIR_BOT ]) ::
    List.map mapper allStates
let notCountVB vbG (q, X, p, op, toCount) =
    if X = vbG then (q, X, p, op, false) else (q, X, p, op, toCount)
let pPDAToKPTSA (maybeDraOriginalMap, draAlphabetIdxMap) macroDefs (PPDAConfig (q0, gamma0)) rules : KPTSA =
    // prepare the virtual bottom for correct standard rules conversion
    let oriQ0 = q0 in
    let oriG0 = gamma0 in
    let gamma0 = VIR_BOT in
    let q0 = VIR_ST in
    let rules = bottomProxyRules oriQ0 oriG0 rules ++ rules in
    // convert to standard rules
    // combine the duplicating rules at first, as when converted to standard rules, duplicating rules should be
    // EXCLUDED rather than combined
    /// the state indexing map for pPDA and gamma index map for BOTH pPDA and (the non-proxy part of) rPTSA
    let qIdxMap', gIdxMap = IndexingTable q0, IndexingTable "$\\bot$" in  // the bottom symbol cannot be ignored
    let rules : PPDARule<int, Gamma> list =
        aggregateList (fun (PPDARule (q, X, prob, p, Xs)) ->
            ((qIdxMap'.lookUp q, gIdxMap.lookUp X, qIdxMap'.lookUp p, List.map (IndexingTable.lookup gIdxMap) Xs),
             prob.eval macroDefs))
            rules
        |> List.map (BiMap.sndMap List.sum)
        |> List.map (fun ((q, X, p, Xs), prob) -> PPDARule (q, X, PEConst prob, p, Xs)) in
    /// all TRANSLATED gammas in pPDA
    let pPDAGammaList : Gamma list = List.init (gIdxMap.getNextIndex () - 1) (fun x -> x + 1) in
    let getProxyGamma : Gamma -> Gamma =
        let BASE = gIdxMap.getNextIndex () - 1 in
        fun gamma -> if gamma = 0 then failwith "Improper cope with bottom" else gamma + BASE in
    /// the DRA Map of the translated pPDA
    let maybeDraMap = flip Option.map maybeDraOriginalMap $ fun map ->
        Map.toSeq map
        |> Seq.map (fun ((q, X), sigma) ->
            ((qIdxMap'.lookUp q, gIdxMap.lookUp X), IndexingTable.lookup draAlphabetIdxMap sigma))
        |> Map.ofSeq in
    /// the indexing map for rPTSA
    let qIdxMap = IndexingTable (SPSOriginal 0) in
    let countRules : HashSet<State * LocalMemory * Gamma * TransOp> = HashSet () in
    let coreRules =
        List.map (pPDARewritingRuleToStdRules Map.empty pPDAGammaList) rules
        |> List.concat
        |> List.map (notCountVB $ gIdxMap.lookUp VIR_BOT)
    in
    let coreRules =
        flip List.map coreRules (fun (q, X, prob, op, count) ->
            let mapOp op : PPDATransOp<State, Gamma> =
                match op with
                | PPDATransState q -> PPDATransState $ qIdxMap.lookUp q
                | PPDATransPush (q, gamma) -> PPDATransPush (qIdxMap.lookUp q, gamma)
                | PPDATransPop q -> PPDATransPop $ qIdxMap.lookUp q in
            ((qIdxMap.lookUp q : State), X, prob, mapOp op, count))
        // remove duplicating rules
        |> aggregateList (fun (q, X, prob, op, count) -> ((q, X, prob, op), count))
        |> List.map (BiMap.sndMap (List.reduce (||)))
        // start conversion
        // direct transition rules
        |> List.map (fun ((q, X, prob, op), count) ->
            let mapOp =
                function
                | PPDATransPush (q, gamma) -> TransUp (q, 1, gamma)
                | PPDATransPop q -> TransDown (q, 3)
                | PPDATransState q -> TransState q in
            (if count then countRules.UnionWith [(q, 0, X, mapOp op); (q, 0, getProxyGamma X, mapOp op)] else ());
            [(q, (0 : LocalMemory), X, prob, mapOp op); (q, 0, getProxyGamma X, prob, mapOp op)])
        |> List.concat in
    // print core rules
    let reversePPDAStateMap =
        qIdxMap'.getRawMap ()
        |> Map.toSeq
        |> Seq.map swap
        |> Map.ofSeq in
    let reverseRPTSAStateMap =
        qIdxMap.getRawMap ()
        |> Map.toSeq
        |> Seq.map swap
        |> Map.ofSeq
    let reverseGammaMap =
        gIdxMap.getRawMap ()
        |> Map.toSeq
        |> Seq.map (fun (name, gIdx) ->
            if gIdx = 0 then [(gIdx, name)]
            else [(gIdx, name); (getProxyGamma gIdx, $"Proxy({name})")])
        |> Seq.concat
        |> Map.ofSeq
    // printers
    let printState q =
        match Map.find q reverseRPTSAStateMap with
        | SPSOriginal ppdaQ -> $"{Map.find ppdaQ reversePPDAStateMap}"
        | SPSRules (ppdaQ, Xs) ->
            let lStr =
                List.map (flip Map.find reverseGammaMap) Xs
                |> printFullSeq in
            $"<{Map.find ppdaQ reversePPDAStateMap}, {lStr}>"
    let printGamma = flip Map.find reverseGammaMap in
    let printLocMem m =
        match m with
        | 0 -> "new"
        | 1 -> "visited"
        | 2 -> "toPop"
        | 3 -> "end"
        | _ -> IMPOSSIBLE () in
    let printOp =
        function
        | TransTer -> "\\top"
        | TransDiv -> "\\Omega"
        | TransUp(q, m, g) -> $"(Up {printState q}, {printLocMem m}, {printGamma g})"
        | TransDown(q, m) -> $"(Down {printState q}, {printLocMem m})"
        | TransState q -> $"{printState q}" in
    let printConfig (q, m, g) = $"{printState q}, {printLocMem m}, {printGamma g}"
    let printRule (q, m, g, p, op) =
        $"({printConfig (q, m, g)}, {p}, {printOp op})"
        +
        if countRules.Contains (q, m, g, op) then " (*)" else ""
    begin
    Flags.RPTSA_DRA_MAPPING <- flip Option.map maybeDraMap $ fun map ->
        Map.toSeq map
        |> Seq.map (fun ((pPDA_q, pPDA_X), sigma) ->
            [((qIdxMap.lookUp $ SPSOriginal pPDA_q, 0, pPDA_X), sigma);
             ((qIdxMap.lookUp $ SPSOriginal pPDA_q, 0, getProxyGamma pPDA_X), sigma)])
        |> Seq.concat
        |> Map.ofSeq
    end;
//    let qList = List.init (qIdxMap.getNextIndex ()) id in
    let qgWorkableList =
        flip List.map coreRules $ (fun (q, _, g, _, _) -> (q, g))
        |> List.filter (snd >> (fun g -> g < gIdxMap.getNextIndex () && g > 0))
        |> List.distinct
    in
    let gamma0Idx = gIdxMap.lookUp gamma0 in
    let auxiliaryRules =
        // the first ones are rules on the bottom
        (0, 0, 0, NUMERIC_ONE, TransUp (0, 1, gIdxMap.lookUp gamma0)) ::
        // for every state, if it reaches the bottom again, then terminates
        List.map (fun q -> (q, 1, 0, NUMERIC_ONE, TransTer))
            (flip List.map coreRules (fun (_, _, g, _, op) ->
                match op with
                | TransDown (q', _) when g = gamma0Idx || g = getProxyGamma gamma0Idx -> [q']
                | _ -> [])
            |> List.concat
            |> List.distinct)
        ++
        // get-to-proxy rules
        (List.map
            (fun (q, g) ->
                [(q, 1, g, NUMERIC_ONE, TransUp (q, 2, getProxyGamma g));
                 (q, 1, getProxyGamma g, NUMERIC_ONE, TransUp (q, 2, getProxyGamma g))])
            qgWorkableList
         |> List.concat)
        ++
        // down-from rules
        (List.map (fun (q, g) ->
            [(q, 2, g, NUMERIC_ONE, TransDown (q, 3));
             (q, 2, getProxyGamma g, NUMERIC_ONE, TransDown (q, 3))])
            qgWorkableList
         |> List.concat)
    begin
    processPrint "===================== Translated rPTSA Rules ========================"
    flip List.iter (coreRules ++ auxiliaryRules) $ (fun rule -> processPrint $"{printRule rule}")
    processPrint "=================== End Translated rPTSA Rules ======================"
    end;
    let rules =
        aggregateList (fun (q, m, g, p, op) -> ((q, m, g), (p, op))) (coreRules ++ auxiliaryRules)
        |> List.filter (fun (config, lst) ->
            (if List.sum (List.map fst lst) > NUMERIC_ONE then failwith $"config: ({printConfig config}) ({config}) has probability > 1.");
            true)
        |> Map.ofList
    in
    let maxQ = qIdxMap.getNextIndex () - 1 in
    let maxM = 3 in
    let maxG = getProxyGamma $ gIdxMap.getNextIndex () - 1 in
    // record the printing information
    Flags.KPTSA_Q_PRINT_TABLE <-
        List.indexed [0..maxQ]
        |> List.map (BiMap.sndMap printState)
        |> Map.ofList;
    Flags.KPTSA_M_PRINT_TABLE <-
        List.indexed [0..maxM]
        |> List.map (BiMap.sndMap printLocMem)
        |> Map.ofList;
    Flags.KPTSA_G_PRINT_TABLE <-
        List.indexed [0..maxG]
        |> List.map (BiMap.sndMap printGamma)
        |> Map.ofList;
    {
        k = 1;
        maxState = maxQ;
        maxLocalMemory = maxM;
        maxGamma = maxG;
        delta = rules;
        kMap = None;
        stateDependencies = None;
        stepCount = Some $ Map.ofSeq (Seq.map (fun x -> (x, NUMERIC_ONE)) countRules);
    }

// ---------------------------------- pPDA End ---------------------------------

// --------------------------------- pBPA Start --------------------------------
type PBPARule =
    PBPARule of
        gamma:string *
        prob:ParseExpr *
        rGammas:string list
let pBPAToKPTSA (mapping, draAlphabetIndices) macroDefs gamma0 rules : KPTSA =
    let rules =
        List.map (fun (PBPARule (X, prob, Xs)) ->
            PPDARule (DUMMY_PBPA_TO_PPDA_STATE, X, prob, DUMMY_PBPA_TO_PPDA_STATE, Xs)) rules
    in
    let mapping = flip Option.map mapping $ fun mapping ->
        Map.toSeq mapping
        |> Seq.map (BiMap.fstMap $ fun X -> (DUMMY_PBPA_TO_PPDA_STATE, X))
        |> Map.ofSeq in
    pPDAToKPTSA (mapping, draAlphabetIndices) macroDefs (PPDAConfig (DUMMY_PBPA_TO_PPDA_STATE, gamma0)) rules
        
// ---------------------------------- pBPA End ---------------------------------

type ParseStrGenRPTSARule =
    ParseStrGenRPTSARule of
        q:string * m:string * g:string * TransOp<string, string, string, CharGen<string, string>>

type ParseModel =
    | ModelStrGenRPTSA of RPTSAConfig * ParseStrGenRPTSARule list
    | ModelPAHORS of TypeDeclPair list * ParsePAHORSRule list
    | ModelRPTSA of RPTSAConfig * RPTSARule list
    | ModelPPDA of PPDAConfig<string, string> * PPDARule<string, string> list
    | ModelPBPA of gamma0:string * PBPARule list
    
// ------------------------------- DRA Start -----------------------------
type DRARule =
    DRARule of
        q:string * sigma:string * nq:string
type DRAMapping =
    | PAHORSMapping of Map<string, string>
    | RPTSAMapping of Map<string * string * string, string>
    | PPDAMapping of Map<string * string, string>
    | PBPAMapping of Map<string, string>
type DRAModel =
    DRAModel of
        q0:string *
        rules:DRARule list *
        accCond:(string list * string list) list *
        mapping:DRAMapping
        
        
// -------------------------------- DRA End ------------------------------

type MacroDecl =
    | MDLetBinding of string * ParseExpr  // let x = Numeric Expression
    | MDConstraint of ParseExpr  // Bool Expression
    
type ModelDef =
    | StrGenRPTSA of
        GeneralRPTSA<string, string, string, CharGen<string, string>>
    | KPTSADef of KPTSA
    | PPDADef of KPTSA
    | PBPADef of KPTSA
    | DirectPPDADef of ProbPDAut<State, Gamma>
    | PAHORSDef of PAHORS
    
type ParseResult =
    ParseResult of
        macros    : Map<string,NumericType> *
        probModel : ModelDef
        // mapping information will be saved in Global.Flags.RPTSA_DRA_MAPPING
    
let toDirectPPDA
        macroDefs
        (PPDAConfig (q0, gamma0))
        (rules : PPDARule<string,string> list) =
    let qMap = IndexingTable () in
    let xMap = IndexingTable () in
    let mapper (PPDARule (q, x, prob, q', xs)) =
        ((qMap.lookUp q,
          xMap.lookUp x),
        (prob.eval macroDefs,
         qMap.lookUp q',
         List.map xMap.lookUp xs))
    in
    let rules = collectToMap $ List.map mapper rules in
    let initSt = qMap.lookUp q0 in
    let botX = xMap.lookUp gamma0 in
    Flags.KPTSA_Q_PRINT_TABLE <- revMap $ qMap.getRawMap ();
    Flags.KPTSA_G_PRINT_TABLE <- revMap $ xMap.getRawMap ();
    { ppdaRules = rules
      ppdaInitSt = initSt
      ppdaBotX = botX }
    
let pBPAToDirectPPDA macroDefs gamma0 pbpaRules =
    let rules =
        flip List.map pbpaRules $ fun (PBPARule (X, prob, Xs)) ->
            PPDARule (DUMMY_PBPA_TO_PPDA_STATE, X,
                      prob,
                      DUMMY_PBPA_TO_PPDA_STATE, Xs)
    in
    toDirectPPDA macroDefs (PPDAConfig (DUMMY_PBPA_TO_PPDA_STATE, gamma0)) rules
    
    
    
    
    
    
// currently, ignore the constraint definitions
let produceModel defs (probModel : ParseModel) =
    // discarded part, but still keep the thing
    let maybeDraModel = None in
    let macroDefs =
        flip (flip List.fold Flags.PRELOAD_BINDINGS) defs $ fun preBindings ->
            function
            | MDConstraint _ -> failwith "Currently not support"
            | MDLetBinding (name, expr) ->
                Map.add name (expr.eval preBindings) preBindings
    in
    let draMapping = Option.map (fun (DRAModel (_, _, _, x)) -> x) maybeDraModel in
    let draAlphabetIdxMap = IndexingTable () in
    let errorMappingNonMatched () = failwith "DRA mapping does not match probabilistic model." in 
    let model =
        match probModel with
        | ModelPAHORS (typeDeclPairs, pahorsRules) ->
            resultPrint $ RReadFormat "PAHORS";
            Flags.CHECK_K <- false;
            // check duplication
            List.map (fun (TypeDeclPair (x, _)) -> x) typeDeclPairs
            |> List.groupBy id
            |> List.iter (snd >> (fun x ->
                if List.length x <> 1 then failwith $"Redefinition of \"{List.head x}\""));
            // type checking
            let ntEnv =
                List.map (fun (TypeDeclPair (x, y)) -> (x, y)) typeDeclPairs
                |> Map.ofList in
            List.iter (typeCheckParseRule ntEnv) pahorsRules;
            let typeDeclPairs, pahorsRules = normalisePAHORSModel typeDeclPairs pahorsRules in
            if Flags.DEBUG then
                let types =
                    List.map toString typeDeclPairs
                    |> String.concat "\n"
                in
                let rules =
                    List.map toString pahorsRules
                    |> String.concat "\n"
                in
                let word =
                    $"Normalised PAHORS Definition:\n%%Types\n{types}\n%%Types\n" +
                    "------------------------------------\n" +
                    $"%%Rules\n{rules}\n%%Rules"
                in
                debugPrint $"{word}";
            let ntMap =
                List.map (fun (TypeDeclPair (x, _)) -> x) typeDeclPairs
                |> List.indexed
                |> List.map swap
                |> Map.ofList in
            let rules, paraLengths, varPrintMap =
                flip List.map pahorsRules (fun x -> x.toPAHORSRule ntMap macroDefs)
                |> List.groupBy (fun (nt, _, _, _) -> nt)
                |> List.sortBy fst
                |> flip List.fold (0, []) (fun (expIdx, ret) (ntIdx, lst) ->
                    if ntIdx <> expIdx then
                        if expIdx = 0 then
                            let (TypeDeclPair (s, _)) = List.head typeDeclPairs in
                            failwith $"No definition for the starting symbol {s}"
                        else (expIdx + 1, ([], [], []) :: ret)
                    else
                        let nRet =
                            flip List.map lst (fun (_, paras, prob, body) -> ((prob, body), List.length paras, Array.ofList paras))
                            |> List.unzip3 in
                        (expIdx + 1, nRet :: ret))
                |> snd
                // debug: after folding, the order of the non-terminals reversed
                |> List.rev
                |> List.unzip3
                |> (fun (x, y, z) -> (Array.ofList $ List.map Array.ofList x,
                                      Array.ofList $ List.map Array.ofList y,
                                      Array.ofList $ List.map Array.ofList z))
            in
            begin
                match draMapping with
                | Some (PAHORSMapping map) ->
                    Map.toSeq map
                    |> Seq.map (fun (nt, sigma) -> (Map.find nt ntMap, draAlphabetIdxMap.lookUp sigma))
                    |> Map.ofSeq
                    |> fun x -> Flags.PAHORS_MAPPING_SOURCE <- Some x
                | None -> ()
                | Some _ -> errorMappingNonMatched ()
            end;
            PAHORSDef {
                nonTerminals =
                    Array.ofList $
                        List.map
                            (fun (TypeDeclPair (_, y)) -> parseTypeToRealType y) typeDeclPairs;
                rules = rules;
                nonCountNonTerminalsBound = List.length typeDeclPairs + 1;
                nonTerminalActualPara = paraLengths;
                nonTerminalPrintTable = Array.ofList (List.map (fun (TypeDeclPair (x, _)) -> x) typeDeclPairs);
                variablePrintTable = varPrintMap;
                countRules = None;
            }
        | ModelRPTSA (rptsaConfig, rptsaRules) ->
            let (RPTSAConfig (k, q0, m0, gamma0)) = rptsaConfig in
            let qIdxMap, mIdxMap, gIdxMap = IndexingTable q0, IndexingTable m0, IndexingTable gamma0 in
            resultPrint $ RReadFormat $"{k}-PTSA";
            let rules =
                flip List.map rptsaRules (fun x -> x.toKPTSARule qIdxMap mIdxMap gIdxMap macroDefs)
                |> aggregateList (fun (q, m, g, p, op) -> ((q, m, g), (p, op)))
                // combine duplicated items
                |> List.map (fun (_, _, g as config, x) ->
                    aggregateList swap x
                    |> List.map (BiMap.sndMap (List.reduce (+)))
                    |> List.map swap
                    |> List.map (fun (prob, op as x) ->
                        match op with
                        | TransDown _ when g = 0 -> (prob, TransTer)
                        | _ -> x)
                    |> fun lst -> (config, lst))
                |> Map.ofList in
            // check validity
            Map.toSeq rules
            |> Seq.iter (fun ((q, m, g), lst) ->
                List.map fst lst
                |> List.sum
                |> fun x ->
                    let recoverMap (idxMap : IndexingTable<_>) =
                        idxMap.getRawMap ()
                        |> Map.toSeq
                        |> Seq.map swap
                        |> Map.ofSeq in
                    if x > NUMERIC_ONE then
                        let q = Map.find q $ recoverMap qIdxMap in
                        let m = Map.find m $ recoverMap mIdxMap in
                        let g = Map.find g $ recoverMap gIdxMap in
                        failwith $"Rules for config {(q, m, g)} has total probability {x} > 1.");
            // store the printing information
            Flags.KPTSA_Q_PRINT_TABLE <- revMap $ qIdxMap.getRawMap ();
            Flags.KPTSA_M_PRINT_TABLE <- revMap $ mIdxMap.getRawMap ();
            Flags.KPTSA_G_PRINT_TABLE <- revMap $ gIdxMap.getRawMap ();
            begin
                match draMapping with
                | Some (RPTSAMapping map) ->
                    Map.toSeq map
                    |> Seq.map (fun ((q, m, g), sigma) ->
                        ((qIdxMap.lookUp q,
                          mIdxMap.lookUp m,
                          gIdxMap.lookUp g),
                         draAlphabetIdxMap.lookUp sigma))
                    |> Map.ofSeq
                    |> fun x -> Flags.RPTSA_DRA_MAPPING <- Some x
                | None -> ()
                | Some _ -> errorMappingNonMatched ()
            end;
            KPTSADef {
                k = k;
                maxState = qIdxMap.getNextIndex ();
                maxLocalMemory = mIdxMap.getNextIndex ();
                maxGamma = gIdxMap.getNextIndex ();
                delta = rules;
                stepCount = None;
                kMap = None;
                stateDependencies = None;
            }
        | ModelStrGenRPTSA (config, rules) ->
            let (RPTSAConfig (k, q0, m0, g0)) = config in
            resultPrint $ RReadFormat $"{k}-TSA";
            let rules =
                flip aggregateList rules (fun (ParseStrGenRPTSARule (q, m, g, op)) ->
                    ((q, m, g), (NUMERIC_ONE, op)))
                |> Map.ofSeq in
            StrGenRPTSA {
                q0 = q0;
                m0 = m0;
                g0 = g0;
                k = k;
                delta = rules;
                kMap = None;
                stateDependencies = None;
                stepCount = None;
            }
        | ModelPPDA (ppdaConfig, ppdaRules) ->
            resultPrint $ RReadFormat "pPDA";
            resultPrint $ RCopeMode (if Flags.DIRECT_PPDA then "pPDA" else "rPTSA");
            Flags.CHECK_K <- false;
            // qX |-> s
            let maybeMap = flip Option.map draMapping $
                            function | PPDAMapping map -> map | _ -> errorMappingNonMatched () in
            if Flags.DIRECT_PPDA then
                DirectPPDADef $ toDirectPPDA macroDefs ppdaConfig ppdaRules
            else
                PPDADef $ pPDAToKPTSA (maybeMap, draAlphabetIdxMap) macroDefs ppdaConfig ppdaRules
        | ModelPBPA (gamma0, pbpaRules) ->
            resultPrint $ RReadFormat "pBPA";
            Flags.CHECK_K <- false;
            // X |-> s
            let maybeMap = flip Option.map draMapping $
                            function | PBPAMapping map -> map | _ -> errorMappingNonMatched () in
            processPrint "Add dummy pPDA control state: \"$\"..."
            if Flags.DIRECT_PPDA then
                DirectPPDADef $ pBPAToDirectPPDA macroDefs gamma0 pbpaRules
            else
                PBPADef $ pBPAToKPTSA (maybeMap, draAlphabetIdxMap) macroDefs gamma0 pbpaRules
    in
    ParseResult (macroDefs, model)
    
    
    
    
    
    
    
    
    
    
    
    

type Model =
    | MKPTSA of KPTSA
    | MPAHORS of PAHORS
    | MPPDA of ProbPDAut<State, Gamma>
    | MSTRRPTSA of GeneralRPTSA<string, string, string, CharGen<string, string>>

/// the three tables for text kPTSA input analysis, should be clear before every analysis
let stateTable = IndexingTable<string> ()
let memoryTable = IndexingTable<string> ()
let gammaTable = IndexingTable<string> ()
/// tables for PAHORS input analysis, should be clear / set to empty before every analysis
let ntTable = IndexingTable ()
let mutable pahorsRulesTable : Map<int, (NumericType * PAHORSTerm<PAHORSSymbol<int, int>>) list> = Map.empty
let mutable varPrintTable : Map<int, string array list> = Map.empty
let mutable actualParaAmountTable : Map<int, int list> = Map.empty
let mutable ntTypes : Map<int, PAHORSType> = Map.empty
/// this set contains count of reverse order -- the rule count is from right to left
let mutable rulesRevCounts = None
let mutable parseBindings : Map<string, NumericType> = Map.empty
let addNewStuffToListOfMap key stuff map =
    Map.add
        key 
        (match Map.tryFind key map with
        | Some l -> stuff :: l
        | None -> [stuff])
        map

let declareNewNtType newNtName ty =
    let ntId =
        try ntTable.createNewIndex newNtName with
        | _ -> failwith $"Re-declare non-terminal: {newNtName}"
    ntTypes <- Map.add ntId (PAHORSType.ToCanonicalForm ty) ntTypes
    
let convertSingleList wrapper (tyList : 'a list) =
    if tyList.Length = 1 then tyList[0]
    else wrapper (Array.ofList tyList)
    
/// raw term -- for parsing purpose.
type ParsingPAHORSTerm =
    | PRSTTTerminate
    | PRSTTDiv
    | PRSTTNonTerminate of int
    | PRSTTVar of string
    | PRSTTProj of int * ParsingPAHORSTerm
    | PRSTTApp of ParsingPAHORSTerm list
    | PRSTTProd of ParsingPAHORSTerm list
    
let termId (s : string) =
    match ntTable.lookUpExistingIndex s with
    | Some i -> PRSTTNonTerminate i
    | None -> PRSTTVar s

let appListTackle (l : ParsingPAHORSTerm list) =
    if l.Length = 1 then l[0]
    else PRSTTApp l

let rec genTermFromRawTerm varMap rawTerm =
    let recall = genTermFromRawTerm varMap
    match rawTerm with
    | PRSTTTerminate -> RSTTApp (RSSTTerminate, [||])
    | PRSTTDiv -> RSTTApp (RSSTDiv, [||])
    | PRSTTNonTerminate ntId -> RSTTApp (RSSTNonTerminal ntId, [||])
    | PRSTTVar vName ->
        match Map.tryFind vName varMap with
        | Some vId -> RSTTApp (RSSTVariable vId, [||])
        | None -> failwith $"Unknown symbol {vName}"
    | PRSTTProj (q, t) ->
        if q < 0 then failwith "Not a valid projection number, note that projection is count from 1."
        RSTTProj (q, recall t)
    | PRSTTProd ql -> RSTTProd (Array.map recall (Array.ofList ql))
    | PRSTTApp rtl ->
        let ht, fl =
            match rtl with
            | ht :: fl -> recall ht, Array.ofList (List.map recall fl)
            | _ -> failwith "Invalid rawTerm."
        match ht with
        | RSTTApp (hs, al) -> RSTTApp (hs, Array.append al fl)
        | RSTTProj _ -> failwith "Not support feature: please only use head-normal application."
        | _ -> failwith "Invalid application."
    
let recordNewRule ntName varList prob rawTerm mark : unit =
    let ntId =
        match ntTable.lookUpExistingIndex ntName with
        | Some id -> id
        | None -> failwith $"Type of non-terminal {ntName} is not declared."
    let varPrintArray = Array.ofList varList
    varPrintTable <- addNewStuffToListOfMap ntId varPrintArray varPrintTable
    actualParaAmountTable <- addNewStuffToListOfMap ntId varPrintArray.Length actualParaAmountTable
    let varMap =
        Map.ofArray (Array.map (fun (i, x) -> (x, i)) (Array.indexed varPrintArray))
    let term = genTermFromRawTerm varMap rawTerm
    pahorsRulesTable <- addNewStuffToListOfMap ntId (prob, term) pahorsRulesTable
    if mark then
        let rc =
            match rulesRevCounts with
            | None ->
                let newRulesCount = HashSet<int * int> ()
                rulesRevCounts <- Some newRulesCount
                newRulesCount
            | Some rc -> rc
        rc.Add (ntId, (Map.find ntId pahorsRulesTable).Length) |> ignore

//type PPDATransOp =
//    | PTOPTer
//    | PTOPDiv
//    | PTOPState of string
//    | PTOPPush of q:string * g:string
//    | PTOPPop of string

// based on the simple algorithm of converting PPDA to rPTSA
//let parsePPDARuleIntoPTSARule qString gString prob op =
//    let q = stateTable.lookUp qString
//    let gamma = gammaTable.lookUp gString
//    let tOp =
//        match op with
//        | PTOPTer -> TransTer
//        | PTOPDiv -> TransDiv
//        | PTOPState qs -> TransState (stateTable.lookUp qs)
//        | PTOPPush (qs, gs) -> TransUp (stateTable.lookUp qs, 1, gammaTable.lookUp gs)
//        | PTOPPop qs -> TransDown (stateTable.lookUp qs, 3)
//    (q, 0, gamma, prob, tOp)

let parseProbStateList tq tm tGamma pqList =
    List.fold
        (fun r (p, q') -> (tq, tm, tGamma, p, TransState q') :: r)
        []
        pqList