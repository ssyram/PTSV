/// Translate PAHORS into GeneralRPTSA rather than KPTSA
/// In this file, we assume the PAHORS used is valid

module PTSV.Translation.PAHORS2GeneralRPTSA

open System.Collections
open System.Collections.Generic
open PTSV.Core
open PTSV.Global
open PTSV.NewEquationBuild
open PTSV.Utils

/// M- elements
type NegativeTransducerMemory =
    | NTMBase
    | NTMProd of memArray:NegativeTransducerMemory list
    | NTMTag of tagID:int * mem:NegativeTransducerMemory
    override x.ToString () =
        match x with
        | NTMBase -> "mu0"
        | NTMProd pl ->
            let mutable ret = "["
            for id, ntm in List.indexed pl do
                ret <- ret + (if id > 0 then ", " else "") + ntm.ToString ()
            ret + "]"
        | NTMTag (tag, ntm) -> $"({tag}, {ntm})"

// all ints are tags, base move is the empty list
type TagList = int list

type GeneralVariable =
    | GVVariable of varID:int
    | GVNonTerminal of ntID:int * ntTag:int

type Moves =
    // GM stands for Game Move
    | GMDirect of moveContent:TagList
    | GMGeneralVariable of vID:GeneralVariable * moveContent:TagList

/// M+ elements
type PositiveTransducerMemory =
    | PTMBase of tag:int
    | PTMTag of tagID:int * mem:PositiveTransducerMemory
    | PTMMoveNegMem of headMove:Moves * negMemList:NegativeTransducerMemory list
    | PTMPosMemNegMemList of
        posMem:(int * PositiveTransducerMemory) * negMemList:NegativeTransducerMemory list

type DeltaNegative = NegativeTransducerMemory * Moves -> PositiveTransducerMemory
type DeltaPositiveValue =
    | DPVTerminate
    | DPVDiverge
    | DPVEpsilon of PositiveTransducerMemory
    | DPVOutput of NegativeTransducerMemory * Moves
type DeltaPositive = PositiveTransducerMemory -> DeltaPositiveValue

type Transducer = DeltaNegative * DeltaPositive * NegativeTransducerMemory

type InterpretationValue = {
    transducer : Transducer
    /// note that this is just an approximation set
    /// there will be double check of the terms
    /// this is because we cannot know if something is used after product and projection
    /// the cost is too high if we keep it exact
    /// while the cost is also high if we keep nothing and try one by one
    /// But this problem should never happen when the opponent is conducting a valid play
    usedVariables : Set<GeneralVariable>
}

/// To prevent rule number from explosion, we should get non-terminals tagged exactly
type NonTerminalTaggedSymbol =
    | NTTSTerminate
    | NTTSDiverge
    | NTTSVariable of int
    | NTTSNonTerminal of ntNo:int * tag:int
/// returns a tagged term and a updating map of the input map
let rec tagNonTerminals term nextIndexMap =
    match term with
    | RSTTApp (s, al) ->
        let headSymbol, nim' =
            match s with
            | RSSTNonTerminal ntNo ->
                let tag, nim =
                    match Map.tryFind ntNo nextIndexMap with
                    | None -> (0, Map.add ntNo 1 nextIndexMap)
                    | Some tag -> (tag, Map.add ntNo (tag + 1) nextIndexMap)
                NTTSNonTerminal (ntNo, tag), nim
            | RSSTDiv -> NTTSDiverge, nextIndexMap
            | RSSTTerminate -> NTTSTerminate, nextIndexMap
            | RSSTVariable vNo -> NTTSVariable vNo, nextIndexMap
        let mutable nim = nim'
        RSTTApp (
            headSymbol,
            Array.map
                (fun t ->
                 let t', nim' = tagNonTerminals t nim
                 nim <- nim'
                 t')
                al), nim
    | RSTTProd pl ->
        let mutable nim = nextIndexMap
        let unionNIM nMap =
            Map.iter
                (fun ntNo idx ->
                 match Map.tryFind ntNo nim with
                 | None -> nim <- Map.add ntNo idx nim
                 | Some oriIdx -> if oriIdx < idx then nim <- Map.add ntNo idx nim)
                nMap
        RSTTProd (
            Array.map
                (fun t ->
                 let t', nim' = tagNonTerminals t nextIndexMap
                 unionNIM nim'
                 t')
                pl), nim
    | RSTTProj (q, t) ->
        let nt, nim = tagNonTerminals t nextIndexMap
        RSTTProj (q, nt), nim

let tagNonTerminalForRuleBody (term : PAHORSTerm<PAHORSSymbol<int, int>>) : PAHORSTerm<NonTerminalTaggedSymbol> =
    let ret, _ = tagNonTerminals term Map.empty
    ret

let getGeneralVariableType (grammar, ntNo) gv =
    match gv with
    | GVVariable vNo ->
        match grammar.nonTerminals[ntNo] with
        | RSTApp al ->
            if vNo >= al.Length - 1 then
                failwith "Trying to get type out of argument range."
            al[vNo]
        | _ -> failwith "This non-terminal should not have parameter."
    | GVNonTerminal (ntNo, _) ->
        grammar.nonTerminals[ntNo]
let retIndexOfAppType (al : 'a array) = al.Length - 1

/// a type with mark recording that if this move has been done
/// also, to speed up:
///     1) record that which product branch has been selected
///     2) record whether this App has begun
type MarkedPAHORSType =
    | MRSTAny
    | MRSTBase of moved:bool
    | MRSTApp of begun:bool * MarkedPAHORSType array
    | MRSTProd of int option * MarkedPAHORSType array
/// get an initial MarkedType from normal types
let rec genMarkedVersionFromPAHORSType ty =
    match ty with
    | RSTAny -> MRSTAny
    | RSTBase -> MRSTBase false
    | RSTApp al -> MRSTApp (false, Array.map genMarkedVersionFromPAHORSType al)
    | RSTProd pl -> MRSTProd (None, Array.map genMarkedVersionFromPAHORSType pl)
/// mark the current move onto a MarkedType
let rec moveOnMarkedType ty move =
    match ty with
    | MRSTAny -> failwith "Cannot move on type Any."
    | MRSTBase mark ->
        if mark then failwith "This move has been made before."
        if move <> [] then failwith "Not a valid move to this type, expect empty move list."
        MRSTBase true
    | MRSTApp (begun, al) ->
        let headTag, mc' =
            match move with
            | ht :: mc' -> ht, mc'
            | _ -> failwith "Not a valid move to this type -- expect a number to specify application branch."
        if headTag >= al.Length then
            failwith "Not a valid move to this type -- application branch specification out of bound."
        if (not begun) && headTag <> retIndexOfAppType al then
            failwith "Not a valid move -- this application has not begun, must make initial move."
        MRSTApp (true,
                 Array.map (fun (i, ty) -> if i = headTag then moveOnMarkedType ty mc' else ty) (Array.indexed al))
    | MRSTProd (branchMark ,pl) ->
        let ht, mc' =
            match move with
            | ht :: mc' -> ht, mc'
            | _ -> failwith "Not a valid move to this type -- expect a number to specify product branch."
        match branchMark with
        | None ->
            if ht >= pl.Length then
                failwith "Not a valid move to this type -- product branch specification out of range."
        | Some bm ->
            if ht <> bm then
                failwith $"Not a valid move -- the move to this branch has been chosen to {bm}"
        MRSTProd
            (Some ht,
             Array.map (fun (i, ty) -> if i = ht then moveOnMarkedType ty mc' else ty) (Array.indexed pl))
/// given a Marked Type, this function gives back in the current situation, what can be further positive moves.
/// Note that not all further positive moves are possible when a negative move is made, please use possibleNextMoves
/// along with the latest move to get true possible moves after a given move.
let rec possiblePositiveMoves (ty : MarkedPAHORSType) : TagList list =
    match ty with
    | MRSTAny -> []
    | MRSTBase _ -> []
    | MRSTApp (begun, al) ->
        if not begun then []
        else List.concat (seq {
            for i in 0 .. al.Length - 2 do
                yield List.map (fun l -> i :: l) (possibleNegativeMoves al[i])
            yield List.map (fun l -> (retIndexOfAppType al) :: l) (possiblePositiveMoves al[al.Length - 1])
        })
    | MRSTProd (branchMark, pl) ->
        match branchMark with
        | None -> []
        | Some bm -> List.map (fun l -> bm :: l) (possiblePositiveMoves pl[bm])
/// if ty is all-unmarked, this function will generate all the initial moves
and possibleNegativeMoves (ty : MarkedPAHORSType) =
    match ty with
    | MRSTAny -> []
    | MRSTBase moved ->
        if moved then []
        else [[]]
    | MRSTApp (begun, al) ->
        if not begun then
            List.map (fun l -> (al.Length - 1) :: l)
                (possibleNegativeMoves al[al.Length - 1])
        else List.concat (seq {
            for i in 0 .. al.Length - 2 do
                yield List.map (fun l -> i :: l) (possiblePositiveMoves al[i])
            yield List.map (fun l -> (retIndexOfAppType al) :: l) (possibleNegativeMoves al[al.Length - 1])
        })
    | MRSTProd (branchMark, pl) ->
        match branchMark with
        | None ->
            List.reduce List.append
                (List.map (fun (i, tl) -> List.map (fun l -> i :: l) tl)
                     (List.indexed (List.map possibleNegativeMoves (List.ofArray pl))))
        | Some bm ->
            List.map (fun l -> bm :: l) (possibleNegativeMoves pl[bm])
/// a supporting function, check if this type is truly untouched in that if all marks are not made
let rec checkAllUntouched ty =
    match ty with
    | MRSTAny -> true
    | MRSTBase moved -> not moved
    | MRSTApp (begun, al) -> ((not begun) && (Array.reduce (&&) (Array.map checkAllUntouched al)))
    | MRSTProd (branchMark, pl) ->
        match branchMark with
        | None -> Array.reduce (&&) (Array.map checkAllUntouched pl)
        | Some _ -> false
/// get all the initial moves that is possible, will firstly check if this type is truly untouched
let getInitialMoves (ty : MarkedPAHORSType) : TagList list =
    if not (checkAllUntouched ty) then failwith "This marked type is not untouched."
    possibleNegativeMoves ty
let getInitialMovesForRawType ty =
    getInitialMoves (genMarkedVersionFromPAHORSType ty)

let rec getValidTermType (grammar, ntNo) term =
    let recall = getValidTermType (grammar, ntNo)
    match term with
    | RSTTApp (hs, al) ->
        let headType =
            match hs with
            | NTTSTerminate -> RSTBase
            | NTTSDiverge -> RSTBase
            | NTTSVariable vId ->
                getGeneralVariableType (grammar, ntNo) (GVVariable vId)
            | NTTSNonTerminal (ntNo, _) ->
                grammar.nonTerminals[ntNo]
        if al.Length = 0 then headType
        else
            match headType with
            | RSTApp tl ->
                if al.Length < tl.Length - 1 then
                    RSTApp (Array.sub tl al.Length (tl.Length - al.Length))
                elif al.Length = tl.Length - 1 then
                    tl[tl.Length - 1]
                else failwith "Invalid type."
            | _ -> failwith "Invalid type."
    | RSTTProd pl -> RSTProd (Array.map recall pl)
    | RSTTProj (tar, t) ->
        match recall t with
        | RSTProd pl -> pl[tar]
        | _ -> failwith "Invalid type."

let ruleBody2Transducer (grammar : PAHORS, ntNo, rNo) : Transducer =
    let term = snd grammar.rules[ntNo].[rNo]
    let term = tagNonTerminalForRuleBody term
    let getGeneralVariableType = getGeneralVariableType (grammar, ntNo)
    let rec interpretTerm (term : PAHORSTerm<NonTerminalTaggedSymbol>) : InterpretationValue =
        match term with
        | RSTTApp (hs, al) ->
            match hs with
            | NTTSTerminate | NTTSDiverge ->
                let deltaPositive =
                    match hs with
                    | NTTSTerminate -> (fun _ -> DPVTerminate)
                    | NTTSDiverge -> (fun _ -> DPVDiverge)
                    | _ -> failwith "Impossible"
                { transducer =
                    ((fun (_, _) -> PTMBase 0),
                     deltaPositive,
                     NTMBase)
                  usedVariables = Set.empty }
            | NTTSVariable varID ->
                headNormalApplicationRule (GVVariable varID) al
            | NTTSNonTerminal (ntNo, tag) ->
                headNormalApplicationRule (GVNonTerminal (ntNo, tag)) al
        | RSTTProd pl -> productRule pl
        | RSTTProj (q, t) -> projectionRule q t
    /// from a term list, get out a list of corresponding deltaNegatives, deltaPositives, and the original
    /// interpreted array itself -- the raw information get from applying interpretation to each term in list
    and analyseTermList tl =
        let infoArray = Array.map interpretTerm tl
        (Array.map
            (fun iv ->
            let argNeg, _, _ = iv.transducer
            argNeg)
            infoArray,
         Array.map
            (fun iv ->
             let _, argPos, _ = iv.transducer
             argPos)
            infoArray,
         infoArray)
    and headNormalApplicationRule headVariable argList : InterpretationValue =
        let mutable usedVariables = Set.add headVariable Set.empty
        /// vmap: variable map -- specify which argument used the variable
        let argNeg, argPos, mu0, vmap =
            let argNeg, argPos, infoArray = analyseTermList argList
            (argNeg,
             argPos,
             NTMProd (List.ofSeq (seq {
                 for iv in infoArray do
                     let _, _, m0 = iv.transducer
                     yield m0
             })),
             (Map.ofArray
                (Array.collect
                    (fun (i, iv) ->
                        usedVariables <- Set.union usedVariables iv.usedVariables
                        Array.zip
                            (Set.toArray iv.usedVariables)
                            (Array.create iv.usedVariables.Count i))
                    (Array.indexed infoArray))))
        /// n
        let argListCount = argList.Length
        // no longer needed, for we will replace sequential 2 with single number
//        // boxing
//        let rec boxing2n n mc =
//            if n <= 0 then mc
//            else boxing2n (n - 1) (2 :: mc)
        /// a change according to remark in the document
        /// rather than taking out and judging positive / minus of moves in delta_+
        /// we finish the packaging / unpacking in this function and delta_+ will be much more easier
        let deltaNegative (nm : NegativeTransducerMemory, oppMove : Moves) =
            /// the true nm content, DO NOT use nm in below
            let ntmList =
                match nm with
                | NTMProd cl -> cl
                | _ -> failwith "Invalid negative memory structure."
            /// i -> opponentMove -> Ci[delta_-^{S_i}(mi, opponentMove)]
            let ciDeltaNegative i opponentMove =
                let mi, negMem =
                    let pre, pos = List.splitAt i ntmList
                    match pos with
                    | mi :: l' -> (mi, List.append pre l')
                    | [] -> failwith "Not valid negative memory."
                let pm = argNeg[i] (mi, opponentMove)
                PTMPosMemNegMemList ((i, pm), negMem)
            match oppMove with
            // o <> (x, _) && o <> (h, _)
            | GMDirect moveContent ->
                if argListCount = 0 then
                    PTMMoveNegMem (GMGeneralVariable (headVariable, moveContent), ntmList)
                else
                    match getGeneralVariableType headVariable with
                    | RSTApp al ->
                        let finalMoveContent =
                            // partial application
                            // just replace the head is OK
                            if argListCount < al.Length - 1 then
                                match moveContent with
                                | headTag :: mc' -> (headTag + argListCount) :: mc'
                                | _ -> failwith "Not a valid player move."
                            elif argListCount = al.Length - 1 then
                                argListCount :: moveContent
                            else failwith "arg list is longer than head type allowed."
                            
                        PTMMoveNegMem (GMGeneralVariable
                            (headVariable, finalMoveContent),
                             ntmList)
                    | _ -> failwith "This head variable is not supposed to have any argument."
            // o = (h, o') OR o = (x, o')
            | GMGeneralVariable (v, moveContent) ->
                // o = (h, o')
                if v = headVariable then
                    if argListCount = 0 then
                        // in this case, headVariable type may not be function type
                        PTMMoveNegMem (GMDirect moveContent, ntmList)
                    else
                        // in this case, headVariable must be of function type
                        let headTag, innerMoveContent =
                            match moveContent with
                            | headTag :: mc' -> headTag, mc'
                            | _ -> failwith "Invalid move for this head variable."
                            
                        if headTag < argListCount then
                            ciDeltaNegative headTag (GMDirect innerMoveContent)
                        else
                            // need to know type of \tau
                            let hvAppLength =
                                match getGeneralVariableType headVariable with
                                | RSTApp al -> al.Length
                                | _ -> failwith "This head variable should not have any argument."
                            let finalMoveContent =
                                // if \tau is not the final return type, shorten headTag
                                if argListCount < hvAppLength - 1 then
                                    (headTag - argListCount) :: innerMoveContent
                                // if \tau is the final return type, there should not be this headTag
                                elif argListCount = hvAppLength - 1 then
                                    innerMoveContent
                                else failwith
                                         $"This head variable should have at most {hvAppLength - 1} arguments
                                           while giving {argListCount}"
                            PTMMoveNegMem (GMDirect finalMoveContent, ntmList)
                        
                                
                    // previous codes with sequential "2"s
//                    let (i, p') =
//                        if argListCount = 0 then (0, moveContent)
//                        else
//                            let rec count2 counter moveContent =
//                                match moveContent with
//                                | 2 :: mc' ->
//                                    if counter + 1 >= argListCount then
//                                        (argListCount, mc')
//                                    else
//                                        count2 (counter + 1) mc'
//                                | 1 :: mc' ->
//                                    (counter, mc')
//                                | _ -> failwith "Not a valid move"
//                            count2 0 moveContent
//                    
//                    // o = (h, o'), o' = (2{n}, p')
//                    if i = argListCount then
//                        PTMMoveNegMem (GMDirect p', ntmList)
//                    else
//                    // o = (h, o'), o' = (2{i - 1}, 1, p')
//                        ciDeltaNegative i (GMDirect p')
                else
                // o = (x, _)
                    match Map.tryFind v vmap with
                    | None -> failwith "Try calling a variable that no argument used. Invalid opponent move."
                    | Some i -> ciDeltaNegative i oppMove
        let deltaPositive (pm : PositiveTransducerMemory) =
            match pm with
            | PTMMoveNegMem (p, negMem) -> DPVOutput (NTMProd negMem, p)
            | PTMPosMemNegMemList ((i, posMem), negMemList) ->
                match argPos[i] posMem with
                | DPVEpsilon posMem' ->
                    DPVEpsilon (PTMPosMemNegMemList ((i, posMem'), negMemList))
                | DPVOutput (negMem, pMove) ->
                    let newNegMem =
                        let pre, pos = List.splitAt i negMemList
                        NTMProd (List.append (List.append pre [negMem]) pos)
                    match pMove with
                    | GMDirect moveContent ->
                        DPVOutput (newNegMem, GMGeneralVariable (headVariable, (i :: moveContent)))
                    | GMGeneralVariable _ -> DPVOutput (newNegMem, pMove)
                | v -> v  // tt or Omega
            | _ -> failwith "Not valid positive memory."
        { transducer = (deltaNegative, deltaPositive, mu0)
          usedVariables = usedVariables }
    and productRule elementaryTermList : InterpretationValue =
        let tlNeg, tlPos, tlMu0, usedVariables =
            let tlNeg, tlPos, infoArray =
                analyseTermList elementaryTermList
            (tlNeg, tlPos,
             Array.map
                (fun iv ->
                 let _, _, m0 = iv.transducer
                 m0)
                infoArray,
             Set.unionMany (seq {
                 for iv in infoArray do
                     yield iv.usedVariables
             }))
        let deltaNegative (negMem, oppMove) =
            let i, trueNegMem, trueOppMove =
                match negMem with
                | NTMBase ->
                    match oppMove with
                    | GMDirect (i :: tl) -> (i, tlMu0[i], GMDirect tl)
                    | _ ->
                        failwith $"Not a valid opponent move, when translating {(grammar.nonTerminalPrintTable[ntNo], rNo)}"
                | NTMTag (i, innerNegMem) ->
                    match oppMove with
                    | GMDirect (i' :: tl) ->
                        if i <> i' then
                            failwith "Not a valid opponent move"
                        (i, innerNegMem, GMDirect tl)
                    | GMGeneralVariable _ ->
                        (i, innerNegMem, oppMove)
                    | _ -> failwith "Not a valid opponent move"
                | _ -> failwith "Not valid negative memory."
            let posMem = tlNeg[i] (trueNegMem, trueOppMove)
            PTMTag (i, posMem)
                    
        let deltaPositive pm =
            let i, ipm =
                match pm with
                | PTMTag (i, ipm) -> (i, ipm)
                | _ -> failwith "Not valid positive memory."
            match tlPos[i] ipm with
            | DPVEpsilon pm' -> DPVEpsilon (PTMTag (i, pm'))
            | DPVOutput (negMem, pMove) ->
                let truePMove =
                    match pMove with
                    | GMDirect tl -> GMDirect (i :: tl)
                    | GMGeneralVariable _ -> pMove
                DPVOutput (NTMTag (i, negMem), truePMove)
            // tt & Omega
            | v -> v
        {
            transducer = (deltaNegative, deltaPositive, NTMBase)
            usedVariables = usedVariables
        }
    and projectionRule projTarget term : InterpretationValue =
        let proxyIV = interpretTerm term
        let proxyNeg, proxyPos, proxyMu0 = proxyIV.transducer
        
        let deltaNegative (negMem, oppMove) =
            let trueOppMove =
                match oppMove with
                | GMDirect tl -> GMDirect (projTarget :: tl)
                | v -> v
            proxyNeg (negMem, trueOppMove)
        
        let deltaPositive pm =
            match proxyPos pm with
            | DPVOutput (negMem, pMove) ->
                DPVOutput (negMem,
                    match pMove with
                    | GMDirect (q :: tl) ->
                        if q <> projTarget then
                            failwith
                               "Not a valid positive return value,
                                possibly because target term for projection is not of valid product type
                                or the given positive memory is not valid."
                        GMDirect tl
                    | v -> v)
            | v -> v
        
        {
            proxyIV with
                transducer = (deltaNegative, deltaPositive, proxyMu0)
        }
    
    (interpretTerm term).transducer

/// NL Formal Proof: this program is guaranteed to terminate & the return term will not contain any instant projection
/// The first part is proved by that every recursive call will be smaller than input t
/// The second part is proved by induction:
/// App, Prod follow immediately from induction hypotheses
/// Proj case, if the case is Prod, the return value depend on tl.[q], which is done by induction hypothesis
/// or, eip t' will not contain ins-proj by IH, if the result is Prod, it is done, or, this is in itself not a ins-proj
let rec eliminateInstantProjection t =
    match t with
    | RSTTApp (s, tl) ->
        RSTTApp (s, Array.map eliminateInstantProjection tl)
    | RSTTProd tl ->
        RSTTProd (Array.map eliminateInstantProjection tl)
    | RSTTProj (q, t') ->
        match t' with
        | RSTTProd tl -> eliminateInstantProjection tl[q]
        | _ ->
            match eliminateInstantProjection t' with
            | RSTTProd tl -> tl[q]
            | v -> RSTTProj (q, v)

/// the state of PTSA
type TransducerState =
    /// only moves of direct or NT are allowed -- direct moves should be interpreted into body moves or var moves
    | TSTMove of Moves
    | TSTTagWithRuleNo of ruleNo:int * actualTS:TransducerState
    | TSTPositiveMemory of PositiveTransducerMemory
    /// for initial NT rule choice
    | TSTInit

/// the first is the rule number of current non-terminal
type TransducerLocalMemory =
    /// stand for all m0, should refer to m0 in transducer to see actual content
    | TLMTM0
    /// the rule number and actual content
    | TLMTLocalMemory of ruleNo:int * negMem:NegativeTransducerMemory
    override x.ToString () =
        match x with
        | TLMTM0 -> "m0"
        | TLMTLocalMemory (rNo, ntm) -> $"(rNo:{rNo}, {ntm})"

//type AutoIncreaseMap<'k when 'k : comparison>(initKey) =
//    let mutable nextValue = 1
//    let mutable table : Map<'k, int> = Map.add initKey 0 Map.empty
//    member x.lookUp key =
//        match Map.tryFind key table with
//        | None ->
//            table <- Map.add key nextValue table
//            nextValue <- nextValue + 1
//            nextValue - 1
//        | Some v -> v
//    
//    member x.getNextIndex () = nextValue
//    member x.getRawMap () = table
        
///// these two will not be needed if we turn sequential 2 into single number
//let rec boxing2s n tl =
//    if n <= 0 then tl
//    else boxing2s (n - 1) (2 :: tl)
//
//let rec extractMoveAppInfo tl =
//    match tl with
//    | 2 :: tl' ->
//        let (c2, rtl) = extractMoveAppInfo tl'
//        (c2 + 1, rtl)
//    | _ -> (0, tl)

// move information for direct types, which should be replaced by actions on marked types
//let rec initOpponentMoves (ty : PAHORSType) : TagList list =
//    match ty with
//    | RSTAny -> []
//    | RSTBase -> [[]]
//    | RSTProd pl ->
//        List.reduce List.append
//            (List.map
//                (fun (i, l) -> List.map (fun v -> (i :: v)) l)
//                (List.indexed (List.ofArray (Array.map initOpponentMoves pl))))
//    | RSTApp sq ->
//        List.map
//            (fun l -> (sq.Length - 1) :: l)
//            (initOpponentMoves (Array.last sq))
//
// this function is not true in that it does not re-tag each return moves.
///// positive is information known by this rule body
//let rec positiveMoves ty =
//    match ty with
//    | RSTAny -> []
//    | RSTBase -> []
//    | RSTApp al -> appReverse negativeMoves positiveMoves al
//    | RSTProd pl -> List.reduce List.append (List.map positiveMoves (List.ofArray pl))
///// a supporting function for pos / neg moves, call func1 for the arg list and call func2 for the ret val.
//and appReverse func1 func2 al =
//    List.concat (seq {
//        for i in 0 .. al.Length - 2 do
//            yield List.map (fun tl -> i :: tl) (func1 al.[i])
//        yield func2 (Array.last al)
//    })
///// negative is information known by environment
//and negativeMoves ty =
//    match ty with
//    | RSTAny -> []
//    | RSTBase -> [[]]
//    | RSTApp al -> appReverse positiveMoves negativeMoves al
//    | RSTProd pl -> List.reduce List.append (List.map negativeMoves (List.ofArray pl))
//
//let rec isPositiveMove ty pMove  =
//    match pMove with
//    | [] ->
//        match ty with
//        | RSTAny -> failwith "Try to make a move in Any."
//        | RSTBase -> false
//        | _ -> failwith "Not a valid move in this type."
//    | headTag :: move ->
//        match ty with
//        | RSTAny -> failwith "Try to move in Any."
//        | RSTBase -> failwith "Not a valid move in this type."
//        | RSTApp al ->
//            if headTag < al.Length - 1 then
//                not (isPositiveMove al.[headTag] move)
//            elif headTag = al.Length - 1 then
//                isPositiveMove al.[headTag] move
//            else failwith "Not a valid move in this type."
//        | RSTProd pl ->
//            if headTag < pl.Length then
//                isPositiveMove pl.[headTag] move
//            else failwith "Not a valid move in this type."
            

///// this version is not complete -- it may produce many impossible moves, we need somehow more exact version
///// it is better to use the marked type version
///// This "opponent" means just the opposite player of the given move
///// And it does not mean to be the opponent player for this type itself
///// Note that this function is an over-approximation -- it may produce some impossible moves in context
///// especially involving product types.
///// This function will NOT produce any initial moves
/////     this can be understood by that there will be at least one move before the moves
/////     Also, one can perform a simple induction to prove this property
//let possibleOpponentMoves (ty : PAHORSType) (pMove : TagList) : TagList list =
//    let isPos = isPositiveMove ty pMove
//    let rec genMoves ty pMove isPos =
//        match ty with
//        | RSTAny -> failwith "Try moving in type Any."
//        | RSTBase ->
//            if pMove <> [] then failwith ""
//            []
//        | RSTProd pl ->
//            match pMove with
//            | projTarget :: pm' ->
//                if projTarget >= pl.Length then
//                    failwith ""
//                genMoves pl.[projTarget] pm' isPos
//            | _ -> failwith ""
//        | RSTApp al ->
//            let headTag, pm' =
//                match pMove with
//                | ht :: pm' -> ht, pm'
//                | _ -> failwith ""
//            // if the move is positive in this level, it means we cannot choose to switch between components
//            if isPos then
//                genMoves al.[headTag] pm' (not isPos)
//            else  // if the move is negative, it means we are fine to switch between components
//                // see if it is going to para or ret
//                if headTag < al.Length - 1 then
//                    // it is para, __^__-
//                    List.concat (seq {
//                        for i, ty in Array.indexed al do
//                            if i = headTag || i = al.Length - 1 then yield []
//                            else yield negativeMoves ty
//                        yield positiveMoves al.[al.Length - 1]
//                        yield genMoves al.[headTag] pm' (not isPos)
//                    })
//                elif headTag = al.Length - 1 then
//                    // it is ret
//                    List.concat (seq {
//                        for i, ty in Array.indexed al do
//                            if i = headTag then yield []  // headTag = al.Length - 1 as stated
//                            else yield negativeMoves ty
//                        yield genMoves al.[headTag] pm' (not isPos)
//                    })
//                else (* it is impossible *) failwith ""
//    try genMoves ty pMove isPos with
//    | exc ->
//        if exc.Message.Length <= 0 then failwith "Not a valid move in this type."
//        raise exc

// a wrong version
// when a player move is given, as opponent, this function computes a list of TagList for possible moves
// we require this pMove be the content of the move in the target type
//let rec possibleOpponentMoves (ty : PAHORSType) (pMove : TagList) : TagList list =
//    match ty with
//    | RSTAny -> failwith "Any cannot make any further moves"
//    | RSTBase ->
//        if pMove <> [] then failwith "Not Valid Player Move."
//        []
//    | RSTApp al ->
//        let headTag, subMove =
//            match pMove with
//            | headTag :: subMove -> headTag, subMove
//            | _ -> failwith "Not a valid move of this type."
//        if headTag >= al.Length then failwith "Not a valid move of this type."
//        let collectAllOtherThisLevelNegativeMoves () =
//            List.reduce List.append
//                (List.map
//                    (fun (i, ty) ->
//                     if i = headTag || i = al.Length - 1 then []
//                     else negativeMoves ty)
//                    (List.ofArray (Array.indexed al)))
//        if headTag < al.Length - 1 then
//        // if the pMove is negative in the current level, it means we can switch between components
//        // and all the negative moves (which is positive in current level) in other components are valid
//        // if the pMove is positive, it means we cannot switch between components, so just continue
//            if isPositiveMove al.[headTag] subMove then
//                // positive in argument is negative in the current level
//                let allOtherThisLevelNegativeMoves =
//                    collectAllOtherThisLevelNegativeMoves ()
//                
//            else possibleOpponentMoves al.[headTag] subMove
//        elif isPositiveMove al.[headTag] subMove then
//            possibleOpponentMoves al.[headTag] subMove
//        else List
//                
//                
//        
//        // a wrong definition -- ignored possible switching between components.
//        let (c2, subMove) = extractMoveAppInfo pMove
//        if c2 < al.Length - 1 then
//            let subMove =
//                match subMove with
//                | 1 :: sm -> sm
//                | _ -> failwith "Invalid move specification."
//            List.map
//                (fun m -> boxing2s c2 (1 :: m))
//                (possibleOpponentMoves al.[c2] subMove)
//        elif c2 = al.Length - 1 then
//            match Array.last al with
//            // when the rightmost elementary move is taken, any initial move from tau_1 to tau_n is possible  
//            | RSTBase ->
//                if subMove <> [] then failwith "Invalid move specification. Expected [] here."
//                List.reduce List.append
//                    (List.map
//                        (fun (c2, ml) -> List.map (fun m -> boxing2s c2 (1 :: m)) ml)
//                        (List.indexed (List.map
//                            initOpponentMoves
//                            (List.ofArray (Array.sub al 0 (al.Length - 1))))))
//            | v -> possibleOpponentMoves v subMove
//        else failwith $"Invalid move specification, expected at most {al.Length - 1} 2s, has: {c2}."
//    | RSTProd pl ->
//        let projTarget, subMove =
//            match pMove with
//            | pt :: sm -> pt, sm
//            | _ -> failwith "Not valid move specification, waiting for projection target."
//        possibleOpponentMoves pl.[projTarget] subMove
        

/// a supporting function for judging if this given move is a positive move for this current type
let rec isPositiveMove ty move =
    match ty with
    | MRSTAny -> failwith "Trying to make a move in type Any."
    | MRSTBase _ ->
        if move <> [] then failwith "Not a valid move in this type -- expect no more tag."
        false
    | MRSTProd (_, pl) ->
        let ht, mc' =
            match move with
            | ht :: mc' -> ht, mc'
            | _ -> failwith "Not a valid move in this type -- expect a tag to specify product branch."
        if ht >= pl.Length then
            failwith "Not a valid move in this type -- product branch specification out of range."
        isPositiveMove pl[ht] mc'
    | MRSTApp (_, al) ->
        let ht, mc' =
            match move with
            | ht :: mc' -> ht, mc'
            | _ -> failwith "Not a valid move in this type -- expect a tag to specify application branch."
        if ht < al.Length - 1 then
            not (isPositiveMove al[ht] mc')
        elif ht = al.Length - 1 then
            isPositiveMove al[ht] mc'
        else
            failwith "Not a valid move in this type -- application branch specification out of bound."
let wrapMovesWith moveList wrapperTag =
    List.map (fun l -> wrapperTag :: l) moveList
/// find the list of moves that can be made from this Marked Type and the previous move to this type.
/// Note that whether the move has been recorded onto this Marked Type does NOT matter.
let possibleNextMoves (ty : MarkedPAHORSType) (move : TagList) : TagList list =
    let isPos = isPositiveMove ty move
    let rec possibleNextMoves ty move isPos =
        match ty, move with
        | MRSTAny, _ -> failwith "Try making a move in Any."
        | MRSTBase _, [] -> []
        | MRSTApp (begun, al), ht :: mc' ->
            // validity check
            if not begun && ht <> (retIndexOfAppType al) then
                failwith "Invalid move: try moving in a type that has not begun."
            
            // if the move is positive in this level, it means we should make negative moves, in application type
            // the branch to go is specified by player (positive) move, so we should just go to where ht specified.
            if isPos then
                wrapMovesWith
                    (possibleNextMoves al[ht] mc' (if ht = retIndexOfAppType al then isPos else not isPos)) ht
            // if the move is negative in this level, it means we should make positive moves, which means we are free
            // to switch between branches
            else List.concat (seq {
                // for arg pos
                for i in 0 .. al.Length - 2 do
                    if i = ht then yield wrapMovesWith (possibleNextMoves al[i] mc' (not isPos)) ht
                    else yield wrapMovesWith (possibleNegativeMoves al[i]) i
                // for ret pos
                if ht <> retIndexOfAppType al then
                    yield wrapMovesWith (possiblePositiveMoves al[retIndexOfAppType al]) (retIndexOfAppType al)
                else yield wrapMovesWith (possibleNextMoves al[ht] mc' isPos) ht
            })
        | MRSTProd (branchMark, pl), ht :: mc' ->
            match branchMark with
            | None -> ()
            | Some bm -> if bm <> ht then failwith "Invalid move: try moving to unselected branch."
            wrapMovesWith (possibleNextMoves pl[ht] mc' isPos) ht
        | _ -> failwith "Invalid move for this type."
            
    possibleNextMoves ty move isPos

///// supporting functions
//let rec branchToAllNextPossibleMoves callBackFunc ty nextMove =
//    let nextType = moveOnMarkedType ty nextMove
//    for move in possibleNextMoves ty nextMove do
//        callBackFunc nextType move
//let callToAllInitialMoves callBackFunc (ty : PAHORSType) =
//    let markedType = markPAHORSType ty
//    for move in getInitialMoves markedType do
//        callBackFunc ty move

/// get a maximum play length from a given type
let getMaximumPlayLength (ty : PAHORSType) : int =
    let markedType = genMarkedVersionFromPAHORSType ty
    let mutable maxCount = 0
    let rec traceLongest mty previousMove currentCount =
        let nextType = moveOnMarkedType mty previousMove
        let nextMoves = possibleNextMoves mty previousMove
        if nextMoves.Length = 0 then
            maxCount <- max maxCount currentCount
        else
            for move in nextMoves do
                traceLongest nextType move (currentCount + 1)
    for initMove in getInitialMoves markedType do
        traceLongest markedType initMove 1
    maxCount
/// for debug, it gives back ONE OF the maximum length play(s)
let DEBUG_getMaximumPlayAndLength (ty : PAHORSType) : TagList list * int =
    let markedType = genMarkedVersionFromPAHORSType ty
    let mutable maxLengthPlay = []
    let mutable maxCount = 0
    let rec traceLongest mty previousMove currentCount currentStack =
        let nextType = moveOnMarkedType mty previousMove
        let nextMoves = possibleNextMoves mty previousMove
        if nextMoves.Length = 0 then
            maxCount <- max maxCount currentCount
            maxLengthPlay <- List.rev currentStack
        else
            for move in nextMoves do
                traceLongest nextType move (currentCount + 1) (move :: currentStack)
    for initMove in getInitialMoves markedType do
        traceLongest markedType initMove 1 [initMove]
    maxLengthPlay, maxCount

/// a much faster way of getting maximum play length, the result is the same as previous
let rec simpleGetMaximumPlayLength ty =
    match ty with
    // any will never have a play, so no length here
    | RSTAny -> 0
    | RSTBase -> 1
    | RSTApp al ->
        // if y is even and x is odd, it means we cannot make use of the last P move of x or y
        Array.reduceBack (fun x y -> x + y - (if x &&& (y + 1) &&& 1 = 1 then 1 else 0))
            (Array.map simpleGetMaximumPlayLength al)
    | RSTProd pl ->
        Array.reduce max (Array.map simpleGetMaximumPlayLength pl)

type ExploredCondition =
    /// under progress
    | ECTProgressing
    /// should not expect further move from this node
    | ECTEndInThisNode
    /// leaving this node with the recorded move and local memory
    /// TransducerState can only reflect moves, not positive mems
    | ECTLeavingThisNode of Moves * TransducerLocalMemory
/// a shared pointer, allow changing content for multiple targets
type ExploredConditionWrapper() =
    let mutable content = ECTProgressing
    member x.set nc = content <- nc
    member x.get () = content

/// if a move is for the non-terminal type, it generates the move for the return type of the rule body
let generateBodyMoveFromNonTerminalMove ruleParaAmount moveContent nonTerminalType =
    if ruleParaAmount = 0 then moveContent
    else
        match nonTerminalType with
        | RSTApp al ->
            match moveContent with
            | ht :: mc' ->
                if ruleParaAmount < al.Length - 1 then
                    // partial application
                    (ht - ruleParaAmount) :: mc'
                elif ruleParaAmount = al.Length - 1 then
                    // full application
                    mc'
                else failwith "Invalid move of this type -- rule argument amount exceeds maximum parameters."
            | _ -> failwith "Invalid move of this type."
        | _ -> failwith "This non-terminal should not have any argument."
/// turn the move of a rule body to be the move of the non-terminal for this rule
let recoverNonTerminalMoveContent ruleParaAmount moveContent nonTerminalType =
    if ruleParaAmount = 0 then moveContent
    else
        // see if the moveContent is for application or not
        match nonTerminalType with
        | RSTApp al ->
            if ruleParaAmount < retIndexOfAppType al then
                // it is a partial application
                match moveContent with
                | ht :: mc' -> (ht + ruleParaAmount) :: mc'
                | _ -> failwith "Not a valid move."
            elif ruleParaAmount = retIndexOfAppType al then
                // it is a complete application
                ruleParaAmount :: moveContent
            else failwith "Not a valid move."
        | _ ->
            failwith $"This non-terminal does not expect argument."

let printMaps
    grammar
    (pTsaStateMap : IndexingTable<TransducerState>)
    (pTsaLocalMemoryMap : IndexingTable<TransducerLocalMemory>)
    (pTsaGammaMap : IndexingTable<(int * int) option>) =
        let printIdMap map idWrapper sWrapper =
            Array.iter (fun (s, id) -> printfn $"{idWrapper id}: {sWrapper s}")
                (Array.sortBy snd (Map.toArray map))
        let rec statePrinter (state : TransducerState) =
            let printMove move =
                match move with
                | GMDirect l -> $"{l}"
                | GMGeneralVariable (gv, m) ->
                    match gv with
                    | GVVariable v -> $"(v{v}: {m})"
                    | GVNonTerminal (ntNo, tag) -> $"({printNonTerminal grammar ntNo}({tag}): {m})"
            match state with
            | TSTInit -> "Init"
            | TSTTagWithRuleNo (tag, s) -> $"(ruleNo:{tag} : {statePrinter s})"
            | TSTMove move -> printMove move
            | TSTPositiveMemory pm ->
                let rec printPositiveMemory pm =
                    match pm with
                    | PTMBase tag -> $"Init{tag}"
                    | PTMTag (tag, pm) -> $"({tag}: {printPositiveMemory pm})"
                    | PTMMoveNegMem (move, negMem) ->
                        $"{{{negMem}; {printMove move}}}"
                    | PTMPosMemNegMemList ((i, pm), negMem) ->
                        $"{{({i}: {printPositiveMemory pm}), {negMem}}}"
                printPositiveMemory pm
        printfn "State map:"
        printIdMap (pTsaStateMap.getRawMap ()) (fun id -> $"q{id}") statePrinter
        printfn "Local Memory map:"
        printIdMap (pTsaLocalMemoryMap.getRawMap ()) (fun id -> $"m{id}") (fun s -> $"{s}")
        let gammaPrinter gamma =
            match gamma with
            | None -> "InitGamma"
            | Some (ntNo, tag) -> $"{printNonTerminal grammar ntNo}({tag})"
        printfn "Gamma map:"
        printIdMap (pTsaGammaMap.getRawMap ()) (fun id -> $"gamma{id}") gammaPrinter

let printMove grammar (ntNo, rNo) move =
    match move with
    | GMDirect mc -> $"{mc}"
    | GMGeneralVariable (GVVariable vNo, mc) -> $"({printVariable grammar (ntNo, rNo) vNo}: {mc})"
    | GMGeneralVariable (GVNonTerminal (ntNo, tag), mc) ->
        $"({printNonTerminal grammar ntNo}({tag}): {mc})"

let addNewRelationToRptsaDraMapping targetNt config =
    Flags.RPTSA_DRA_MAPPING <- flip Option.map Flags.PAHORS_MAPPING_SOURCE $ fun map ->
        let oriMap = Option.defaultValue Map.empty Flags.RPTSA_DRA_MAPPING in
        match Map.tryFind targetNt map with
        | None -> oriMap
        | Some sigma -> Map.add config sigma oriMap
//    if Option.isNone Global.Flags.PAHORS_MAPPING_SOURCE then ()
//    else
//        if Option.isNone Global.Flags.RPTSA_DRA_MAPPING then
//            Flags.RPTSA_DRA_MAPPING <- Some Map.empty

let rec printPositiveMemoryWithProjCount grammar (ntNo, rNo) pm =
    let printNtmList ntmList =
        let mutable ret = ""
        for idx, ntm in List.indexed ntmList do
            ret <- ret + (if idx > 0 then ", " else "") + ntm.ToString ()
        ret
    match pm with
    | PTMBase tag -> $"\mu+{{{tag}}}"
    | PTMTag (tag, pm') -> $"(Branch:{tag}, {printPositiveMemoryWithProjCount grammar (ntNo, rNo) pm'})"
    | PTMMoveNegMem (move, ntmList) ->
        "{[" + printNtmList ntmList + $"], move:{printMove grammar (ntNo, rNo) move}" + "}"
    | PTMPosMemNegMemList ((i, posMem), ntmList) ->
        $"{{pos:({i}, {printPositiveMemoryWithProjCount grammar (ntNo, rNo) posMem}), [" + printNtmList ntmList + "]}"

let rec printDPV grammar s dpv =
    match dpv with
    | DPVTerminate -> "tt"
    | DPVDiverge -> "Omega"
    | DPVEpsilon pm -> printPositiveMemoryWithProjCount grammar s pm
    | DPVOutput (ntm, pMove) ->
        $"{{{ntm.ToString ()} | {printMove grammar s pMove}}}"

//let printMove grammar (ntNo, rNo) move =
//    let rec printInType ty move =
//        match ty, move with
//        | RSTAny, _ -> "T"
//        | RSTBase, [] -> "*"
//        | RSTApp al, ht :: mc' ->
//            Array.fold
//                (fun s (id, ty) ->
//                    let addParenIfApp s =
//                        match ty with
//                        | RSTApp _ -> $"({s})"
//                        | _ -> s
//                    s + addParenIfApp (if id = ht then printInType ty mc' else printType ty))
//                ""
//                (Array.indexed al)
//        | RSTProd pl ->
//          

/// analyse the move on the current type, see if it is the var move or rule body move.
let unpackDirectMove (grammar : PAHORS) (ntNo, rNo) move = 
    match grammar.nonTerminals[ntNo] with
    | RSTApp al ->
        let paraAmount = grammar.nonTerminalActualPara[ntNo][rNo]
        let ht, mc' =
            match move with
            | ht :: mc' -> ht, mc'
            | _ -> failwith "Not a valid move of this type."
        if ht < paraAmount then
            GMGeneralVariable (GVVariable ht, mc')
        else GMDirect (generateBodyMoveFromNonTerminalMove paraAmount move (RSTApp al))
    | _ -> GMDirect move

let rec printTransducerState grammar ntRuleInfo tst =
    let recall = printTransducerState grammar ntRuleInfo
    match tst with
    | TSTInit -> "Init"
    | TSTTagWithRuleNo (rNo, ts) -> $"(rNo:{rNo}, {recall ts})"
    | TSTMove move -> $"Move ({printMove grammar ntRuleInfo move})"
    | TSTPositiveMemory pm -> $"Positive Memory ({printPositiveMemoryWithProjCount grammar ntRuleInfo pm})"

/// called by the need of use of DRA algorithm, we should collect the new Up states
type TranslatingResult<'q,'m,'g>
    when 'q : comparison and 'm : comparison and 'g : comparison
    =
    { rptsa : GeneralRPTSA<'q,'m,'g,TerOp>
      /// all the initial moves at the new ups
      newUpStates : Set<'q>
      /// the source PAHORS -- so one can print the value better from the translated rptsa
      grammar : PAHORS }

let translateToGeneralRPTSA (grammar : PAHORS) : TranslatingResult<_,_,_> =
    // eliminate all instant projections -- that is: \pi{i} <t1, ..., tn> --> ti
    let grammar =
        {
            grammar with
                rules =
                    let rawRules =
                        Array.map
                            (Array.map
                                 (if Flags.ELIMINATE_INSTANT_PROJECTION then
                                    (fun (p, t) -> (p, eliminateInstantProjection t))
                                  else id))
                            (Array.map
                                (Array.filter (fun (p, _) -> p > NUMERIC_ZERO && p <= NUMERIC_ONE))
                                grammar.rules)
                    // for those non-terminal whose rules are all precluded, we add an probability 1 Omega rule.
                    // for non-terminal without any rule is not allowed.
                    Array.map
                        (fun ruleArray ->
                            if Array.length ruleArray = 0 then
                                [|NUMERIC_ONE, RSTTApp (RSSTDiv, [||])|]
                            else ruleArray)
                        rawRules
        }
    
    let q0 = TSTInit in
    let m0 = TLMTM0 in
    let gamma0 = None in
    /// (Moves + Positive Transducer Memory + Initial) -> State
    /// Initial is for rule body choice of S (start NT)
    let pTsaStateMap = IndexingTable(q0)
    /// Negative Transducer Memory -> Local Memory
    let pTsaLocalMemoryMap = IndexingTable(m0)
    /// (NtNo * NtTag) option -> Gamma
    /// None -> Initial gamma, for rule body choice of S (start NT)
    let pTsaGammaMap = IndexingTable(gamma0)
    /// q, m, gamma, op |-> step count (better None-0)
    let mutable stepCount = Map.empty
    
    let transducers =
        let ts =
            Array.map
                (fun (ntNo, ruleList) ->
                    Array.map
                        (fun (rNo, (_, _)) -> ruleBody2Transducer (grammar, ntNo, rNo))
                        (Array.indexed ruleList))
                (Array.indexed grammar.rules)
        if not Flags.INNER_DEBUG then ts
        else
            let mapping (ntNo, ar) =
                let mapping (rNo, (dN, dP, m0)) =
                    let printString =
                        $"For {rNo} rule of {printNonTerminal grammar ntNo}: " + printRule grammar (ntNo, rNo)
                    let newNegative (negMem, oMove) =
                        printfn $"{printString}"
                        let posMem = dN (negMem, oMove)
                        let s =
                            "\delta-: " +
                                negMem.ToString () + (if negMem = m0 then "{M0}" else "") +
                                $", {printMove grammar (ntNo, rNo) oMove} |-> " +
                                printPositiveMemoryWithProjCount grammar (ntNo, rNo) posMem
                        printfn $"{s}\n"
                        posMem
                    let newPositive pm =
                        printfn $"{printString}"
                        let ret = dP pm
                        let s = $"\delta+: {printPositiveMemoryWithProjCount grammar (ntNo, rNo) pm} |-> " +
                                    printDPV grammar (ntNo, rNo) ret
                        printfn $"{s}\n"
                        ret
                    (newNegative, newPositive, m0)
                Array.map mapping (Array.indexed ar)
            Array.map mapping (Array.indexed ts)
    
    let mutable pTsaDelta = Map.empty
    
    let addNewRule k (e, count) =
        let q, m, gamma = k
        let _, op = e
        if count > uint64 0 then
            stepCount <- Map.add (q, m, gamma, op) (NumericType count) stepCount
        match Map.tryFind k pTsaDelta with
        | None ->
            pTsaDelta <- Map.add k [e] pTsaDelta
        | Some l ->
            pTsaDelta <- Map.add k (e :: l) pTsaDelta
    
    begin
        let initGamma = pTsaGammaMap.lookUp (Some (0, 0))
        // add DRA Mappings
        addNewRelationToRptsaDraMapping 0 (* the starting symbol *) (0, 0, 0) (* the initial config *)
        
        // if there are more than one rules, there is no probabilistic choice
        // initial moves
        for rNo, (p, _) in Array.indexed grammar.rules[0] do
            // q_{Move(o)}^{rNo}
            let q = pTsaStateMap.lookUp (TSTTagWithRuleNo (rNo, TSTMove (GMDirect [])))
            let stepCount =
                match grammar.countRules with
                | Some cr ->
                    if cr.Contains (0, rNo) then 1
                    else 0
                | None -> 1
            addNewRule (0, 0, 0) ((p, OpTransUp (q, 0, initGamma)), uint64 stepCount)
    end
    
    let unionTagMaps m1 m2 =
        let mutable map = m1
        Map.iter
            (fun k idx ->
             match Map.tryFind k map with
             | None -> map <- Map.add k idx map
             | Some oriIdx -> if oriIdx < idx then map <- Map.add k idx map)
            m2
        map
    
    let nonTerminalTagMap =
        // bugfix : the beginning set should be empty, the following should be added right after
        /// the initial tag map for tag map collection
        /// this is because the start symbol must be mentioned at least one time.
        let initialTagMap = Map.empty
//        Array.reduce unionTagMaps
//            (Array.map
//                (fun lst ->
//                    (Array.reduce unionTagMaps
//                        (Array.map
//                            (fun (_, t) ->
//                                let _, ret = tagNonTerminals t initialTagMap
//                                ret)
//                            lst)))
//                grammar.rules)
        let eachRuleTagMap =
            Array.map
                (Array.map
                    (fun (_, t) ->
                        let _, ret = tagNonTerminals t initialTagMap
                        ret))
                grammar.rules
        let res =
            Array.reduce unionTagMaps
                (Array.map (Array.reduce unionTagMaps) eachRuleTagMap)
        match Map.tryFind 0 res with
        | Some _ -> res
        | None ->
            // if S is not mentioned, the first S should be added
            Map.add 0 1 res
    
    /// records: when a state is given to some gamma with specified local memory, what are the possible states back
    /// and the back local memory
    let mutable statesDependencies = Hashtable()
    let lookUpStatesDependencies (key : State * LocalMemory * Gamma) =
        let ret = statesDependencies[key]
        (if ret = null then
            statesDependencies.Add(key, HashSet<State * LocalMemory> ())
            statesDependencies[key]
         else ret) :?> HashSet<State * LocalMemory>
    
    let iterFunc ntNo tagAmount : unit =
        let mutable exploredMap : Map<State * LocalMemory, ExploredConditionWrapper> = Map.empty
        let rulesOfCurrentNt = grammar.rules[ntNo]
        
        /// the latest up configuration
        let downStack = Stack<State * LocalMemory> ()
        // temporarily no need to do so
//        let upStacks = Hashtable ()
//        let findUpStacks gamma =
//            let ret = upStacks.[gamma]
//            (if ret = null then
//                upStacks.Add(gamma, Stack<State> ())
//                upStacks.[gamma]
//             else ret) :?> Stack<State>
        
        let addNewStatesDependenciesToEachTag moveContent localMemory =
            for tag in 0 .. tagAmount - 1 do
                let q = TSTMove (GMGeneralVariable (GVNonTerminal (ntNo, tag), moveContent))
                let tq = pTsaStateMap.lookUp q
                let tm = pTsaLocalMemoryMap.lookUp localMemory
                let tGamma = pTsaGammaMap.lookUp (Some (ntNo, tag))
                // the coming q and coming m
                let cq, cm = downStack.Peek()
                (lookUpStatesDependencies (cq, cm, tGamma)).Add(tq, tm) |> ignore
        
        /// to analyse starting configurations, which means q is a move to this place
        /// currentMarkedTypes is a map: "(ntNo, tag) option -> MarkedType", None is for the current node itself.
        let rec analyseStartConfig (q, m) currentMarkedTypes : unit =
            // here, q is definitely a move, and we add this move -- a new move into this current node
            // we push the current move to be the "current node".
            /// compute the push function and pop function for pushing and popping the current q
            let pushFunc, popFunc =
                /// if it is a move from downside, we push this q to downStack.
                let pushDown () =
                    let tq = pTsaStateMap.lookUp q
                    let tm = pTsaLocalMemoryMap.lookUp m
                    downStack.Push(tq, tm)
//                let pushUp gamma = ()
//                    let tq = pTsaStateMap.lookUp q
//                    (findUpStacks gamma).Push(tq)
                let popDown () = downStack.Pop () |> ignore
//                let popUp gamma =
////                    (findUpStacks gamma).Pop () |> ignore
                match q with
                | TSTTagWithRuleNo _ ->
                    // this is definitely a move from downside.
                    pushDown, popDown
                | TSTMove move ->
                    match move with
                    | GMDirect _ ->
                        // if it is a move for this type itself, it means it is coming from downside.
                        pushDown, popDown
                    | GMGeneralVariable (GVNonTerminal (*(upNt, upTag)*) _, _) ->
                        ignore, ignore
//                        let gamma = pTsaGammaMap.lookUp (Some (upNt, upTag))
//                        (fun () -> pushUp gamma), (fun () -> popUp gamma)
                    | _ -> failwith "INTERNAL: impossible move."
                | _ -> failwith "INTERNAL: impossible start q."
            
            // push the current q information 
            pushFunc ()
            
            let nExploredCondition = ExploredConditionWrapper()
            // bugfix : this place, q should contain the whole type, a leaving move must not have that var types
            /// if the leaving move and memory is the given lMove and lMemory
            /// this function explore all possible opponent moves back to this node by
            /// making use of the current marked types given.
            /// Just predict the next possible back moves by the leaving move and the current marked types.
            /// Then put in to generate a new analysis for start configs
            /// The impossibility of infinite loops is guaranteed by the finiteness of total moves of a marked type.
            let exploreNewOpponentMovesWithCurrentMarkedTypes (lMove, lMemory) =
                nExploredCondition.set (ECTLeavingThisNode (lMove, lMemory))
                match lMove with
                | GMDirect pMove ->
                    // bugfix : this should be done directly
                    let thisNtMarkedType = Map.find None currentMarkedTypes
                    let pMoveMarkedType =
                        moveOnMarkedType thisNtMarkedType pMove
                    // bugfix : this should be placed here to cope with the shortcut created
                    addNewStatesDependenciesToEachTag pMove lMemory
                    for oMove in possibleNextMoves thisNtMarkedType pMove do
                        let nextMarkedTypes =
                            Map.add None (moveOnMarkedType pMoveMarkedType oMove) currentMarkedTypes
                        // bugfix : mark this oMove in the type
                        analyseStartConfig (TSTMove (GMDirect oMove), lMemory) nextMarkedTypes
                | GMGeneralVariable (GVVariable _, _) ->
                    failwith "INTERNAL: Invalid State -- tagged with var type."
                | GMGeneralVariable (GVNonTerminal (upNtNo, upTag), moveContent) ->
                    let key = Some (upNtNo, upTag)
                    let upNtMarkedType =
                        match Map.tryFind key currentMarkedTypes with
                        | Some mt -> mt
                        | None -> genMarkedVersionFromPAHORSType grammar.nonTerminals[upNtNo]
                    let upMoveMarkedType =
                        moveOnMarkedType upNtMarkedType moveContent
                    for pMove in possibleNextMoves upNtMarkedType moveContent do
                        // bugfix : mark this pMove in the type
                        let nextMarkedTypes =
                            Map.add key (moveOnMarkedType upMoveMarkedType pMove) currentMarkedTypes
                        analyseStartConfig
                            (TSTMove (GMGeneralVariable (GVNonTerminal (upNtNo, upTag), pMove)), lMemory)
                            nextMarkedTypes
                            
            
            /// to conduct real analysis until leaving this node or end in this node
            let rec analyseInternalConfig (iq : TransducerState, im : TransducerLocalMemory) : unit =
                checkTimeOut ()
                let tiq = pTsaStateMap.lookUp iq
                let tim = pTsaLocalMemoryMap.lookUp im
                let addNewRuleToEachTagFromCurrentConfig genV =
                    for tag in 0 .. tagAmount - 1 do
                        let tGamma = pTsaGammaMap.lookUp (Some (ntNo, tag))
                        addNewRule (tiq, tim, tGamma) (genV tag)
                match Map.tryFind (tiq, tim) exploredMap with
                | Some ec ->
                    match ec.get () with
                    | ECTProgressing ->
                        // if it is currently progressing, it means it is a loop, just end this loop
                        // for the probability is 1, just end all of the conditions
                        nExploredCondition.set ECTEndInThisNode
                    | ECTEndInThisNode ->
                        // if the current node has been explored and there is nothing to do with other moves
                        // just end here
                        nExploredCondition.set ECTEndInThisNode
                    | ECTLeavingThisNode (lMove, lMemory) ->  // stands for leaving q, leaving m
                        // if it will finally lead to a new (q, m) set
                        // use the current marked type to analyse new stuff for this leaving memory
                        exploreNewOpponentMovesWithCurrentMarkedTypes (lMove, lMemory)
                | None ->
                    // this means it should continue going through this current configuration.
                    // first add explore for this current config
                    exploredMap <- Map.add (tiq, tim) nExploredCondition exploredMap
                    // has validation, no need to check this below
                    let rNo =
                        match iq, im with
                        | TSTTagWithRuleNo (rNo, (TSTMove _ | TSTPositiveMemory _)), TLMTM0 -> rNo
                        | (TSTMove _ | TSTPositiveMemory _), TLMTLocalMemory (rNo, _) -> rNo
                        | _, _ -> failwith "Rule Number information should be included in q OR m."
                    let deltaNegative, deltaPositive, m0 = transducers[ntNo][rNo]
                    
                    /// give the new positive memory and the wrapper for the new state (whether to tag with ruleNo)
                    /// this function conduct all works when the new state is a positive memory
                    let toPositiveMemory pm qWrapper =
                        // remains in this node, no need to set exploreCondition
                        let nq = qWrapper (TSTPositiveMemory pm)
                        let tnq = pTsaStateMap.lookUp nq
                        addNewRuleToEachTagFromCurrentConfig (fun _ -> ((NUMERIC_ONE, OpTransState tnq), 0uL))
                        analyseInternalConfig (nq, im)
                    
                    /// conduct all real works given a move and the current negative memory
                    /// finally, it will wrap the generated q with qWrapper
                    /// as this will not change m, just use `im`.
                    let analyseFromMove move negMem qWrapper =
                        // unpack move first -- if it is for this current nt (GMDirect), it should be unpacked into
                        // whether var or body move
                        let trueMove =
                            match move with
                            | GMGeneralVariable (GVNonTerminal _, _) -> move
                            | GMDirect dMove -> unpackDirectMove grammar (ntNo, rNo) dMove
                            | _ -> failwith "INTERNAL: variable move should not appear."
                        let pm = deltaNegative (negMem, trueMove)
                        toPositiveMemory pm qWrapper
                    
                    /// conduct real works when given a positive memory
                    /// finally, it wrap the generated q with qWrapper
                    /// this will not use the current local memory
                    /// m will always be wrapped with the current ruleNo --
                    ///     if it is not output, just use im
                    ///     if it is output, leaving this node must tag the new local memory with ruleNo
                    let analyseFromPositiveMemory pm qWrapper =
                        match deltaPositive pm with
                        | DPVTerminate ->
                            // we not add any count here, as that should be made when normalisation
                            addNewRuleToEachTagFromCurrentConfig (fun _ -> (NUMERIC_ONE, OpTransSp SpTer), uint64 0)
                            nExploredCondition.set ECTEndInThisNode
                        | DPVDiverge ->
                            addNewRuleToEachTagFromCurrentConfig (fun _ -> (NUMERIC_ONE, OpTransSp SpDiv), uint64 0)
                            nExploredCondition.set ECTEndInThisNode
                        | DPVEpsilon pm' ->
                            // this is not possible in effect, but add just for robustness
                            toPositiveMemory pm' qWrapper
                        | DPVOutput (negMem, pMove) ->
                            // going up or down from the current node
                            let newLocalMemory = TLMTLocalMemory (rNo, negMem)
                            let tNewLocalMemory = pTsaLocalMemoryMap.lookUp newLocalMemory
                            /// n
                            let ruleParaAmount = grammar.nonTerminalActualPara[ntNo][rNo]
                            let currentNonTerminalType = grammar.nonTerminals[ntNo]
                            match pMove with
                            | GMDirect moveContent ->
                                // a direct move on the return value of this rule
                                // ask the caller of the rule (downside node) to pass the control onto
                                // constitute the complete move tag list of the non-terminal
                                let ntMoveContent =
                                    recoverNonTerminalMoveContent
                                        ruleParaAmount
                                        moveContent
                                        currentNonTerminalType
                                addNewRuleToEachTagFromCurrentConfig
                                    (fun tag ->
                                        let nq = (TSTMove
                                                      (GMGeneralVariable
                                                           (GVNonTerminal (ntNo, tag), ntMoveContent)))
                                        let tnq = pTsaStateMap.lookUp nq
                                        (NUMERIC_ONE, OpTransDown (tnq, tNewLocalMemory)), uint64 0)
                                    
//                                // add new dependencies
//                                addNewStatesDependenciesToEachTag ntMoveContent newLocalMemory
                                // explore possible moves back from below.
                                exploreNewOpponentMovesWithCurrentMarkedTypes (GMDirect ntMoveContent, newLocalMemory)
                            | GMGeneralVariable (GVVariable vNo, moveContent) ->
                                // any variable move is actually a move asking for content in this current NT
                                // so just goes down
                                // first, recover the move in the whole non-terminal
                                let ntMoveContent = vNo :: moveContent
                                addNewRuleToEachTagFromCurrentConfig
                                    (fun tag ->
                                        let nq = (TSTMove
                                                      (GMGeneralVariable
                                                           (GVNonTerminal (ntNo, tag), ntMoveContent)))
                                        let tnq = pTsaStateMap.lookUp nq
                                        (NUMERIC_ONE, OpTransDown (tnq, tNewLocalMemory)), uint64 0)
                                    
//                                // add new dependencies
//                                addNewStatesDependenciesToEachTag ntMoveContent newLocalMemory
                                // explore possible moves back from below.
                                exploreNewOpponentMovesWithCurrentMarkedTypes (GMDirect ntMoveContent, newLocalMemory)
                            | GMGeneralVariable (GVNonTerminal (upNtNo, upTag), moveContent) ->
                                // this means to go up, we should firstly know if the move is within initial move
                                // which means q should be tagged with ruleNo or not.
                                let upGamma = (upNtNo, upTag)
                                let tUpGamma = pTsaGammaMap.lookUp (Some upGamma)
                                if List.contains
                                       moveContent
                                       (getInitialMovesForRawType grammar.nonTerminals[upNtNo]) then
                                    // usually, we should have step count 1, but if it is virtually added node, no need
                                    let stepCount = if ntNo > grammar.nonCountNonTerminalsBound then 0 else 1
                                    for upRuleNo, (p, _) in Array.indexed grammar.rules[upNtNo] do
                                        let stepCount =
                                            match grammar.countRules with
                                            | Some cr ->
                                                if cr.Contains (upNtNo, upRuleNo) then 1
                                                else 0
                                            | None -> stepCount
                                        // bugfix : when it is going up, q should not be tagged with nt and tag
                                        addNewRuleToEachTagFromCurrentConfig
                                            (fun tag ->
                                                // add DRA Mapping
                                                addNewRelationToRptsaDraMapping upNtNo
                                                    (tiq, tim, pTsaGammaMap.lookUp (Some (ntNo, tag)));
                                                // add actual rules
                                                let nq = (TSTTagWithRuleNo (upRuleNo, (TSTMove (GMDirect moveContent))))
                                                let tnq = pTsaStateMap.lookUp nq
                                                // the first time getting up to a place, should have step count 1
                                                // but if it is within the non-count bound, should not add step count
                                                (p, OpTransUp (tnq, tNewLocalMemory, tUpGamma)), uint64 stepCount)
                                else
                                    addNewRuleToEachTagFromCurrentConfig
                                        (fun _ ->
                                            let nq = TSTMove (GMDirect moveContent)
                                            let tnq = pTsaStateMap.lookUp nq
                                            // from the second up to a same place, should have step count 0
                                            (NUMERIC_ONE, OpTransUp (tnq, tNewLocalMemory, tUpGamma)), uint64 0)
                            
                                // explore possible moves back from above.
                                exploreNewOpponentMovesWithCurrentMarkedTypes (pMove, newLocalMemory)
                            
                        
                    /// a support function.
                    let wrapQWithRuleNo q = TSTTagWithRuleNo (rNo, q)
                    
                    match iq, im with
                    | TSTTagWithRuleNo (_, TSTMove move), _ ->
                        // to pm, with rule No.
                        analyseFromMove move m0 wrapQWithRuleNo
                    | TSTMove move, TLMTLocalMemory (_, negMem) ->
                        // to pm
                        analyseFromMove move negMem id
                    | TSTTagWithRuleNo (_, TSTPositiveMemory pm), _ ->
                        // to all other places, with rule No.
                        analyseFromPositiveMemory pm wrapQWithRuleNo
                    | TSTPositiveMemory pm, _ ->
                        // to all other places, but current local memory does not matter now
                        analyseFromPositiveMemory pm id
                    | _, _ -> failwith "Impossible."
            
            analyseInternalConfig (q, m)
            
            // pop the current q information
            popFunc ()
        
        let markedType = genMarkedVersionFromPAHORSType grammar.nonTerminals[ntNo]
        let initialOpponentMoves = getInitialMoves markedType
        for initMove in initialOpponentMoves do
            for rNo in 0 .. rulesOfCurrentNt.Length - 1 do
                // bugfix : this should be the whole type, and unpack should be done within the analysis
//                /// the initial moves must be for the return type, not for the whole type.
//                let trueInitMove =
//                    let argNum = grammar.nonTerminalActualPara.[ntNo].[rNo]
//                    generateBodyMoveFromNonTerminalMove argNum initMove grammar.nonTerminals.[ntNo]
                analyseStartConfig
                    (TSTTagWithRuleNo (rNo, TSTMove (GMDirect initMove)), TLMTM0)
                    (Map.add None (moveOnMarkedType markedType initMove) Map.empty)
    
    Map.iter iterFunc nonTerminalTagMap
    
    // compute k
    let maxPlayLengths =
        Array.map simpleGetMaximumPlayLength grammar.nonTerminals
    let fromMaxPlayLengthToK mpl = (mpl + 1) / 2
    let k = fromMaxPlayLengthToK (Array.max maxPlayLengths)
    let kMap =
        Map.ofArray
            (Array.map
                (fun (tag, ntNo) ->
                    (Map.find (Some (ntNo, tag)) (pTsaGammaMap.getRawMap ()),
                     fromMaxPlayLengthToK maxPlayLengths[ntNo]))
                (Array.collect
                    (fun (ntNo, tagAmount) -> Array.indexed (Array.create tagAmount ntNo))
                    (Map.toArray nonTerminalTagMap)))
    
    if Flags.DEBUG then
        printMaps grammar pTsaStateMap pTsaLocalMemoryMap pTsaGammaMap
    
    // the original stateDependencies information maybe useful as values of 
    
    let statesDependencies =
        Map.ofSeq (seq {
            for p in statesDependencies do
                let p = p :?> DictionaryEntry
                let q, _, gamma = p.Key :?> State * LocalMemory * Gamma
                yield ((q, gamma),
                       Set.toList
                           (Set.map fst
                               (Set.ofSeq
                                    (seq {yield! p.Value :?> HashSet<State * LocalMemory>}))))
        })
    
    if Flags.INNER_DEBUG then
        let printQList qList =
            (List.fold
                (fun r q ->
                    let s = if r = "[" then "" else ", "
                    r + s + $"q{q}")
                "["
                qList) + "]"
        Array.iter
            (fun ((q, gamma), qList) ->
                printfn $"(q{q}, g{gamma}) |-> {printQList qList}")
            (Array.sortBy (fun ((_, gamma), _) -> gamma) (Map.toArray statesDependencies))
    
    let getRevMap (idxMap : IndexingTable<_>) =
        Map.toSeq (idxMap.getRawMap ())
        |> Seq.map swap
        |> HashMap.fromSeq
    in
    let stateRevMap : HashMap<int, TransducerState> = getRevMap pTsaStateMap in
    let locMemRevMap : HashMap<int, TransducerLocalMemory> = getRevMap pTsaLocalMemoryMap in
    let gammaRevMap : HashMap<int, (Gamma * int) option> = getRevMap pTsaGammaMap in
//    let rec printState st =
//        match stateRevMap[st] with
//        | TSTInit -> "q0"
//        | TSTMove moves ->
//            match moves with
//            | GMDirect m ->
//                $"DMove({printFullSeq m})"
//            | GMGeneralVariable (gv, m) ->
//                match gv with
//                | GVVariable varId ->
//                    $"VarMove({varId}, {printFullSeq m})"
//                | GVNonTerminal (ntNo, ntTag) ->
//                    $"NtMove({grammar.nonTerminalPrintTable[ntNo]}, {ntTag}, {printFullSeq m})"
    
    let mapOp op =
        match op with
        | OpTransState st -> OpTransState stateRevMap[st]
        | OpTransUp (q, m, g) ->
            OpTransUp (stateRevMap[q], locMemRevMap[m], gammaRevMap[g])
        | OpTransDown (q, m) ->
            OpTransDown (stateRevMap[q], locMemRevMap[m])
        | OpTransSp SpTer -> OpTransSp SpTer
        | OpTransSp SpDiv -> OpTransSp SpDiv in
    
    let rules =
        Map.toSeq pTsaDelta
        |> Seq.map (fun ((q, m, g), lst) ->
            ((stateRevMap[q], locMemRevMap[m], gammaRevMap[g]),
             flip List.map lst $ fun (p, op) ->
                 (p, mapOp op)))
        |> Map.ofSeq
    in
    
    let kMap =
        Map.toSeq kMap
        |> Seq.map (BiMap.fstMap (flip HashMap.find gammaRevMap))
        |> Map.ofSeq
    in
    
    let statesDependencies =
        Map.toSeq statesDependencies
        |> Seq.map (fun ((q, g), lst) ->
            ((stateRevMap[q], gammaRevMap[g]),
             List.map (flip HashMap.find stateRevMap) lst))
        |> Map.ofSeq
    in
    
    let stepCount =
        Map.toSeq stepCount
        |> Seq.map (fun ((q, m, g, op), sc) ->
            ((stateRevMap[q],
              locMemRevMap[m],
              gammaRevMap[g],
              mapOp op),
              sc))
        |> Map.ofSeq
    in
    
    let rptsa =
        { q0 = q0
          m0 = m0
          g0 = gamma0
          k = k
          delta = rules
          kMap = Some kMap
          stateDependencies = Some statesDependencies
          stepCount = Some stepCount }
    
//    let rptsa = 
//        {   k = k
//            maxState = pTsaStateMap.getNextIndex ()
//            maxLocalMemory = pTsaLocalMemoryMap.getNextIndex ()
//            maxGamma = pTsaGammaMap.getNextIndex ()
//            delta = pTsaDelta
//            kMap = Some kMap
//            stateDependencies = Some statesDependencies
//            stepCount = Some stepCount   } in
        
    /// initial move contents
    let initMoves = Array.map getInitialMovesForRawType grammar.nonTerminals
                    |> Seq.concat
                    |> seqToHashSet in 
        
    let newUpStates = pTsaStateMap.getRawMap ()
                      |> Map.toSeq
                      |> Seq.filter (fun (st, _) -> match st with
                                                    | TSTTagWithRuleNo (_, TSTMove (GMDirect mc)) ->
                                                        initMoves.Contains mc
                                                    | _ -> false)
                      |> Seq.map snd
                      |> Set.ofSeq in
    let newUpStates = Set.map (flip HashMap.find stateRevMap) newUpStates in
        
    { rptsa = rptsa
      newUpStates = newUpStates
      grammar = grammar }
