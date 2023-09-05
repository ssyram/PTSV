module PTSV.Input

open System.Collections.Generic
open System.IO
open FSharp.Text.Lexing
open PTSV.Core
open ParserSupport
open PTSV.Global
open Utils

module CodeInput =
    let genKPTSA (k : int) (trans : TransRuleList) : KPTSA =
        let mutable delta = Map.empty
        let mutable maxState = 0
        let mutable maxMemory = 0
        let mutable maxGamma = 0
        let addNewItem rule =
            let q, m, gamma, p, op = rule
            match delta.TryFind (q, m, gamma) with
            | None -> delta <- Map.add (q, m, gamma) ((p, op) :: []) delta
            | Some l -> delta <- Map.add (q, m, gamma) ((p, op) :: l) delta
        let updateThreeVar q m gamma =
            if q > maxState then maxState <- q
            if m > maxMemory then maxMemory <- m
            match gamma with
            | None -> ()
            | Some gamma ->
                if gamma > maxGamma then maxGamma <- gamma
        for rule in trans do
            addNewItem rule
            let q, m, gamma, _, op = rule
            updateThreeVar q m (Some gamma)
            match op with
            | TransUp(q', m', gamma') -> updateThreeVar q' m' (Some gamma')
            | TransDown (q', m') -> updateThreeVar q' m' None
            | TransState q' -> if q' > maxState then maxState <- q'
            | _ -> ()
        let ret : KPTSA =
            { k = k
              maxState = maxState
              maxLocalMemory = maxMemory
              maxGamma = maxGamma
              delta = delta
              kMap = None
              stateDependencies = None
              stepCount = None }
        ret
        
module TextInput =
    /// will make use of environmental things
    let generatePAHORS () : PAHORS =
        let generateArrayFromTable table =
            let l = snd (Array.unzip (Array.sortBy fst (Map.toArray table)))
            Array.map Array.ofList l
        let rules = generateArrayFromTable pahorsRulesTable
        let rc =
            match rulesRevCounts with
            | None -> None
            | Some rc ->
                Some (HashSet (seq {
                    for ntNo, reverseRuleNo in rc do
                        yield (ntNo, rules.[ntNo].Length - reverseRuleNo)
                }))
        { nonTerminals = snd (Array.unzip (Array.sortBy fst (Map.toArray ntTypes)))
          rules = rules
          nonTerminalActualPara = generateArrayFromTable actualParaAmountTable
          nonTerminalPrintTable = ntTable.toArray ()
          variablePrintTable = generateArrayFromTable varPrintTable
          nonCountNonTerminalsBound = ntTypes.Count
          countRules = rc }
    
    // based on the simple algorithm of converting PPDA to rPTSA
    let parsePPDADef (rules : TransRuleList) =
        // firstly, spare gamma0 for true bottom
        let mutable rules =
            List.map
                (fun (q, m, gamma, p, op) ->
                    let op =
                        match op with
                        | TransUp (q', m', gamma') -> TransUp (q', m', gamma' + 1)
                        | _ -> op
                    (q, m, gamma + 1, p, op))
                rules
        // add the initial rule
        rules <- (0, 0, 0, NUMERIC_ONE, TransUp (0, 3, 1)) :: rules
        rules <- List.sortBy (fun (_, _, g, _, _) -> g) rules
        let oriRules = rules
        let mutable nextPossibleGamma =
            let _, _, g, _, _ =
                List.last rules
            g + 1
        let upToItself gamma =
            List.fold
                (fun b (_, _, g, _, op) ->
                    let nb =
                        if g <> gamma then false
                        else
                            match op with
                            | TransUp (_, _, g') -> g' = gamma
                            | _ -> false
                    b || nb)
                false
                oriRules
        // count gamma from 1 because 0 is spared for bottom
        for gamma in 1 .. gammaTable.getNextIndex () do
            if upToItself gamma then
                // create a new proxy gamma with all the same behavior
                // add when m = m1 go to the proxy node and turn itself to m2 for both origin and proxy
                // when m = m2, just go down for both origin and proxy
                let proxyGamma =
                    nextPossibleGamma <- nextPossibleGamma + 1
                    nextPossibleGamma - 1
                let iterFunc (q, m0, g, p, op) =
                    if g = gamma then
                        rules <- (q, m0, proxyGamma, p, op) :: rules
                List.iter iterFunc oriRules
                for q in 0 .. stateTable.getNextIndex () - 1 do
                    rules <- (q, 1, gamma, NUMERIC_ONE, TransUp (q, 2, proxyGamma)) :: rules
                    rules <- (q, 1, proxyGamma, NUMERIC_ONE, TransUp (q, 2, proxyGamma)) :: rules
                    rules <- (q, 2, gamma, NUMERIC_ONE, TransDown (q, 3)) :: rules
                    rules <- (q, 2, proxyGamma, NUMERIC_ONE, TransDown (q, 3)) :: rules
            else
                for q in 0 .. stateTable.getNextIndex () - 1 do
                    // m = m1 then create a new proxy node, convert the current to redundant
                    rules <- (q, 1, gamma, NUMERIC_ONE, TransUp (q, 2, gamma)) :: rules
                    // m = m2 then this is a redundant node, just pass
                    rules <- (q, 2, gamma, NUMERIC_ONE, TransDown (q, 3)) :: rules
        
        let ret = CodeInput.genKPTSA 1 rules
        // for rules with epsilon loops, rather than epsilon elimination, we should 
        let stepCount =
            List.fold
                (fun rm (q, m, gamma, _, op) ->
                    // this gamma0 is not a true bottom, so we should ignore this step
                    // if m <> 0, this is just a structural rule, does not correspond to any single step
                    if gamma = 0 || m <> 0 || op = TransTer then rm
                    else
                        Map.add (q, m, gamma, op) NUMERIC_ONE rm)
                Map.empty
                rules
        if Flags.DEBUG then
            printfn "Input Map:"
            let qWrapper n = $"q{n}"
            let gammaWrapper n = $"gamma{n + 1}"
            printfn "State Maps:"
            printfn $"{stateTable.printTableContent qWrapper}"
            printfn "Gamma Maps:"
            printfn $"{gammaTable.printTableContent gammaWrapper}"
        let ret =
            {
                ret with stepCount = Some stepCount
            }
        printfn $"Generated 1-PTSA: \n{ret}"
        ret
    
    /// use Parser & Lexer to tackle also the comment
    let parseString (s : string) =
        stateTable.clear ()
        memoryTable.clear ()
        gammaTable.clear ()
        ntTable.clear ()
        rulesRevCounts <- None
        pahorsRulesTable <- Map.empty
        varPrintTable <- Map.empty
        actualParaAmountTable <- Map.empty
        ntTypes <- Map.empty
        parseBindings <- Flags.PRELOAD_BINDINGS
        let lexbuf = LexBuffer<char>.FromString s
        // initialise the line from line 1
        lexbuf.EndPos <- lexbuf.EndPos.NextLine;
        try
            let (ParseResult (_macros, model)) = Parser.file Lexer.token lexbuf in
            let model =
                match model with
                | KPTSADef model ->
                    MKPTSA model
                | PAHORSDef pahors ->
                    MPAHORS pahors
                | PPDADef model ->
                    MKPTSA model
                | DirectPPDADef model ->
                    MPPDA model
                | PBPADef model ->
                    MKPTSA model
                | StrGenRPTSA model ->
                    MSTRRPTSA model
            in
            model
        with
        | e ->
            let es =
                $"Unexpected Token: \"{System.String(lexbuf.Lexeme)}\". At line {lexbuf.StartPos.Line}, " +
                $"column {lexbuf.StartPos.Column}."
            eprintfn $"{es}"
            reraise ()
    
    let parseFile (filePath : string) =
        let s =
            use sr = new StreamReader (filePath)
            sr.ReadToEnd ()
        in
        parseString s