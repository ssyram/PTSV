module PTSV.MultipleContextFreeGrammar

open Microsoft.FSharp.Collections
open Utils
open PTSV.Global
open PTSV.ShortAlgorithms

/// the default ToString is just to extract the information without tagging
type MCFGSymbol<'t, 'var> =
    | Terminal of 't
    | Variable of 'var
    override x.ToString () =
        match x with
        | Terminal    t   -> toString t
        | Variable    var -> toString var

/// nt1(v11, ..., v1m1) ... ntn(vn1, ..., vnmn)
type RightHandSide<'nt, 'var> = ('nt * 'var list) list

/// (s1, ..., sk)
type LeftHandSide<'t, 'var> = MCFGSymbol<'t, 'var> list list

/// the reduction of an MCFG rule
let ruleReduction (lhs : LeftHandSide<_,_>, rhs : RightHandSide<_,_>)
    (rhsVal : _ list list) : LeftHandSide<_,_> =
    // register each variable symbol to its exact position in the value
    let varDims =
        List.map snd rhs
        |> List.map List.indexed
        |> List.indexed
        |> List.map (fun (ntNo, lst) ->
            List.map (fun (varNo, varSym) -> 
                (varSym, (ntNo, varNo))) lst)
        |> List.concat
        |> Map.ofSeq in
    let findVar varSym =
        let ntNo, varNo = Map.find varSym varDims in
        rhsVal[ntNo].[varNo] in
    flip List.map lhs $ fun strs ->
        List.map (function Terminal t -> [Terminal t] | Variable varSym -> findVar varSym) strs
        |> List.concat

let printMCFGRule nt lhs rhs =
    let symsToString lst =
        List.map toString lst
        |> String.concat " " in
    let lhs =
        List.map symsToString lhs
        |> String.concat ", " in
    let ntVarsToString (nt, vars) =
        List.map toString vars
        |> String.concat ", "
        |> fun x -> $"{nt} ({x})" in
    let rhs =
        List.map ntVarsToString rhs
        |> String.concat "; " in
    $"{nt} ({lhs}) <- {rhs}."

type MultipleContextFreeGrammar<'nt, 't, 'var>
    when 'nt : comparison and 't : comparison
    =
    {
        nonTerminals : Map<'nt, uint>
        terminals : Set<'t>
        rules : Map<'nt, (LeftHandSide<'t, 'var> * RightHandSide<'nt, 'var>) list>
        startNonTerminal : 'nt
    }
    override x.ToString () =
        let nts =
            Map.toSeq x.nonTerminals
            |> Seq.map toString
            |> String.concat "\n\t"
            |> fun x -> $"{{\n\t{x}\n}}" in
        let terminals =
            Set.toSeq x.terminals
            |> Seq.map toString
            |> String.concat ", "
            |> fun x -> $"{{{x}}}" in
        let rules =
            Map.toSeq x.rules
            |> Seq.map (fun (nt, lst) ->
                List.map (uncurry $ printMCFGRule nt) lst
                |> String.concat "\n\t"
                |> fun x -> $"\n\t{x}")
            |> String.concat ""
        in
        "{\n" +
        $"Non-Terminals:\n{nts}\n" +
        $"Terminals:\n{terminals}\n" +
        $"Rules:\n{{{rules}\n}}\n" +
        $"Starting Non-Terminal: {x.startNonTerminal}\n" +
        "}"

exception InvalidMCFGException of string

/// throws the reason of invalidity if exists
let checkMCFGValidity mcfg =
    // check if the starting symbol has only one dimension
    begin
        match Map.tryFind mcfg.startNonTerminal mcfg.nonTerminals with
        | Some 1u -> ()
        | _       -> raise $ InvalidMCFGException "The starting symbol is not declared to have dimension 1."
    end
    let checkRule nt (lhs, rhs) =
        // check lhs dimension
        match Map.tryFind nt mcfg.nonTerminals with
        | Some dim ->
            if dim <> uint (List.length lhs) then
                raise $ InvalidMCFGException
                    $"Rule \"{printMCFGRule nt lhs rhs}\" does not match the declared dimension {dim}."
        | None ->
            raise $ InvalidMCFGException $"Non-terminal {nt} is not declared."
        // check linearity of variables used
        List.map (List.map (function Variable v -> [v] | _ -> [])) lhs
        |> List.concat
        |> List.concat
        |> List.countBy id
        |> List.iter (fun (v, count) ->
            if count > 1 then
                raise $ InvalidMCFGException
                    $"In Rule \"{printMCFGRule nt lhs rhs}\", the LHS variable {v} is used for {count} times.")
        // check match of variables
        let vars =
            List.map snd rhs
            |> List.concat
            |> Set.ofSeq in
        List.iter (List.iter (function
            | Variable v ->
                if not $ Set.contains v vars then
                    raise $ InvalidMCFGException
                        $"In Rule \"{printMCFGRule nt lhs rhs}\", the LHS variable {v} is undefined."
            | _ -> ())) lhs
        // check duplication of variables
        List.map snd rhs
        |> List.concat
        |> List.countBy id
        |> List.iter (fun (v, count) ->
            if count > 1 then
                raise $ InvalidMCFGException
                    $"In Rule \"{printMCFGRule nt lhs rhs}\", the RHS variable {v} is re-defined.")
    in
    Map.toSeq mcfg.rules
    |> Seq.iter (fun (nt, lst) -> List.iter (checkRule nt) lst)

type EnumerateContext<'t, 'nt, 'var> when 'nt : comparison =
    {
        enumConstantRule : Map<'nt, LeftHandSide<'t, 'var> list>
        enumRecursiveRule : Map<'nt, (LeftHandSide<'t, 'var> * RightHandSide<'nt, 'var>) list>
    }
    
// we should also replace the pure rules in order to enumerate rules
let mkEnumerateCtx mcfg =
    Map.toSeq mcfg.rules
    |> Seq.map (fun (nt, lst) ->
        List.partition (snd >> List.isEmpty) lst
        |> BiMap.pairMap (
            (fun x -> (nt, List.map fst x)),
            (fun x -> (nt, x))))
    |> List.ofSeq
    |> List.unzip
    |> BiMap.pairMap (Map.ofSeq, Map.ofSeq)
    |> fun (cons, proc) ->
        { enumConstantRule = cons
          enumRecursiveRule  = proc }

exception NoWordWithThisIndexException

/// may get stuck and run infinitely if the MCFG is pathological that some non-terminal may get stuck
/// For example:
/// When the only rule for F is: F(x) <- F(x).
let rec enumerateNonTerminalWord ctx nt idx =
    let consRules = Option.defaultValue [] $ Map.tryFind nt ctx.enumConstantRule in
    let consToRet lhs =
        let mapper lst = flip List.map lst $ function Terminal t -> t | _ -> IMPOSSIBLE () in
        List.map mapper lhs in
    let len = List.length consRules in
    if idx < len then
        consToRet consRules[idx]
    else
        // to enumerate the proceed rules
        let idx = idx - len in
        let recRules = Map.find nt ctx.enumRecursiveRule in
        let recRulesAmount = List.length recRules in
        // loop to find the suitable rule to enumerate
        let ruleId = idx % recRulesAmount in
        let rule = recRules[ruleId] in
        let nextIdx = idx / recRulesAmount in
        let rhsDist = Enumerate.getMultipleDimensions (List.length $ snd rule) nextIdx in
        let rhsVal =
            List.zip rhsDist (snd rule)
            |> List.map (fun (idx, (nt, vars)) -> List.zip vars (enumerateNonTerminalWord ctx nt idx))
            |> List.concat
            |> Map.ofSeq in
        let mapper segment =
            List.map (function | Terminal t -> [t] | Variable v -> Map.find v rhsVal) segment
            |> List.concat in
        List.map mapper $ fst rule

let private generateAllConstantStrings mcfg =
    let initRules = Option.defaultValue [] (Map.tryFind mcfg.startNonTerminal mcfg.rules) in
    if not $ List.forall (snd >> List.isEmpty) initRules then None
    else
        Some $ List.map (fst >> List.map (List.map (function Terminal t -> t | _ -> IMPOSSIBLE ()))) initRules

let private reduceCons consMap (lhs, rhs : RightHandSide<_,_>)
    : (LeftHandSide<_,_> * RightHandSide<_,_>) list =
    // the RHS to return
    let realRhs = List.filter (fst >> flip Map.containsKey consMap >> not) rhs in
    // a list of ``a value list of tuples of strings''
    let rec genRhsVals rhs =
        match rhs with
        | [] -> [[]]
        | (nt, vars) :: rhs ->
            match Map.tryFind nt consMap with
            | None ->
                List.map (fun lst -> List.map (fun x -> [Variable x]) vars :: lst) (genRhsVals rhs)
            | Some lhsLst ->
                List.allPairs lhsLst (genRhsVals rhs)
                |> List.map List.Cons
    in
    List.map (ruleReduction (lhs, rhs)) (genRhsVals rhs)
    |> List.map (fun x -> (x, realRhs))

/// returns an MCFG with no purely constant non-terminal
/// except the case when the starting symbol is itself a contant symbol
let rec private substituteConstants mcfg =
    let consMap, nonConsRules =
        Map.toList mcfg.rules
        |> List.partition (snd >> List.forall (snd >> List.isEmpty))
        // the first is the constant rules and the second the non-constant rules
        |> BiMap.fstMap (List.map (BiMap.sndMap (List.map fst)))
        |> BiMap.fstMap Map.ofList
    in
    if Map.isEmpty consMap then mcfg
    else
        match Map.tryFind mcfg.startNonTerminal consMap with
        | None ->
            if Flags.DEBUG then
                Map.toSeq consMap
                |> Seq.map (fst >> toString)
                |> String.concat ", "
                |> fun x -> printfn $"Erased Constant Non-Terminals: {x}";
            let nonConsRules =
                List.map (BiMap.sndMap (List.map (reduceCons consMap) >> List.concat)) nonConsRules
                |> Map.ofList in
            let nonTerminals = Map.filter (fun nt _ -> not $ Map.containsKey nt consMap) mcfg.nonTerminals in
            let mcfg = { nonTerminals = nonTerminals
                         terminals = mcfg.terminals
                         rules = nonConsRules
                         startNonTerminal = mcfg.startNonTerminal } in
            // continue until no constant rule exist
            substituteConstants mcfg
        | Some rules ->
            if Flags.DEBUG then
                printfn "The start symbol is a constant variable.";
            // simply return the finite language
            { nonTerminals = Map.ofList [(mcfg.startNonTerminal, 1u)]
              terminals = mcfg.terminals
              rules = Map.ofList [(mcfg.startNonTerminal, List.map (fun x -> (x, [])) rules)]
              startNonTerminal = mcfg.startNonTerminal }

let enumerateMCFGWords mcfg =
    // there has to be some modifications in order to make the enumeration works systematically
    // that all strings are guaranteed to be enumerated if run infinitely
    // the first is: to replace the non-terminals with only constant rules but not recursive rules
    // especially, if the starting non-terminal is constant we simply return all the strings that exist
    let mcfg = substituteConstants mcfg in
    if Flags.DEBUG then
        printfn $"MCFG to enumerate:\n{mcfg}"
    match generateAllConstantStrings mcfg with
    | Some lst -> List.toSeq lst
    | None ->
        // afterwards, enumerate the values
        let ctx = mkEnumerateCtx mcfg in
        Seq.initInfinite (fun idx ->
            try enumerateNonTerminalWord ctx mcfg.startNonTerminal idx
            with
            | NoWordWithThisIndexException -> [[]])
