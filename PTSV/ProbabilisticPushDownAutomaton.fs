module PTSV.ProbabilisticPushDownAutomaton

open PTSV
open Global
open PTSV.NewEquationBuild
open Utils
open Core

// This file defines the stuff related to pPDA

let printSingleRule q x (p, q', xs) =
    List.map printG xs
    |> printSeq "" " "
    |> fun lst -> $"{printQ q} {printG x} -({p})-> {printQ q'} {lst}"

type ProbPDAut<'q, 'x>
    when 'q : comparison
    and  'x : comparison = {
    ppdaRules : Map<'q * 'x, (NumericType * 'q * 'x list) list>
    ppdaInitSt : 'q
    ppdaBotX : 'x
} with
    override this.ToString () =
        let rules =
            Map.toList this.ppdaRules
            |> List.collect (fun ((q, x), lst) ->
                List.map (printSingleRule q x) lst)
        in
        "pPDA Def: {\n" +
        "  q0 = " + toString this.ppdaInitSt + ",\n" +
        "  bot = " + toString this.ppdaBotX + ",\n" +
        "  rules: {\n" +
        "    " + printSeq "" "\n    " rules + "\n" +
        "  }\n" +
        "}"


/// The `downMap` of a given X -- what is the possible down qs from a given direction
let private ppdaDownMap ppda =
    let fMapper lst =
        flip List.filter lst (fun (_, _, lst) -> List.isEmpty lst)
        |> List.map (fun (_,x,_) -> x)
    in
    Map.toList ppda.ppdaRules
    |> List.map (BiMap.pairMap (snd, fMapper)) //  ('x * ('q list)) list
    |> aggregateList id
    |> List.map (BiMap.sndMap (List.concat >> Set.ofList))
    |> Map.ofList

type IToRawVar<'q, 'g>
    when 'q : comparison
    and  'g : comparison =
    interface
        abstract ToRawVar : ProbPDAut<'q, 'g> -> RawVar<'q, 'g>
    end

/// Defines only the `down` var
type PDVar<'q, 'g>
    when 'q : comparison
    and  'g : comparison = PDVar of 'q * 'g * 'q
    with
    interface IToRawVar<'q, 'g> with
        member this.ToRawVar _ =
            match this with
            | PDVar (q, x, q') -> VTrips ([ q; q' ], x)
    override x.ToString () =
        match x with
        | PDVar (q, x, q') -> $"<{printQ q} | {printG x} | {printQ q'}>"

/// The variable to be appeared in the equation system
type EqVar<'q, 'g> 
    when 'q : comparison
    and  'g : comparison =
    | EVNorm of PDVar<'q, 'g>
    | EVX0
    interface IToRawVar<'q, 'g> with
        member this.ToRawVar ppda =
            match this with
            | EVX0 -> VTer ([ ppda.ppdaInitSt ], ppda.ppdaBotX)
            | EVNorm var -> (var :> IToRawVar<_,_>).ToRawVar ppda
    override x.ToString () =
        match x with
        | EVNorm var -> var.ToString ()
        | EVX0 -> "x0"

type PpdaRHS<'q, 'g> 
    when 'q : comparison
    and  'g : comparison = PpdaRHS of (NumericType * PDVar<'q, 'g> list)

/// the private building context
type private PpdaEqSysConsCtx<'q, 'g>
    when 'q : comparison
    and  'g : comparison (ppda : ProbPDAut<'q, 'g>) =
    let dMap = ppdaDownMap ppda
    let mutable result = []
    /// { v |-> IsStructuralZero }
    let cacheRes = HashMap<PDVar<'q, 'g>, bool> ()
    let initXDownQs =
        Map.tryFind ppda.ppdaBotX dMap
        |> Option.defaultValue Set.empty
        |> Set.toList
    
    
    
    let lastHasQ' q' xs =
        let lastX = List.last xs in
        match Map.tryFind lastX dMap with
        | Some set -> Set.contains q' set
        | None     -> false
    
    
    /// q(i-1) qn [Xi ... Xn] |-> [ <q(i-1) Xi qi> ... <q(n-1) Xn qn> ]
    let rec consVsTerm qiM1 qn xs =
        match xs with
        | []        -> [ [] ]
        | xi :: lst ->
            let downQs =
                match lst with
                | [] -> [ qn ]  // if `i == n`, so the down `q` is `qn`
                | _  -> // otherwise, try all kinds of possible downs
                        Map.tryFind xi dMap
                        |> Option.defaultValue Set.empty
                        |> Set.toList
            in
            let qiCol qi =
                /// <q(i-1) Xi qi>
                let var = PDVar (qiM1, xi, qi) in
                if buildVar var then
                    // this variable is Structurally Zero 
                    // so NO NEED to further build
                    // or log this item
                    []
                else
                    // <qi X(i+1) q(i+1)> ... <q(n-1) Xn qn>
                    consVsTerm qi qn lst
                    |> List.map (currying List.Cons var)
            in
            List.collect qiCol downQs
    
    
    /// Given a variable, construct the equation system RHS
    and consRHS (PDVar (q, x, q') as var) =
        let collector (p, q0, xs as t) =
            debugSameLinePrint $
                $"\rExploring {var}: " +
                printSingleRule q x t
            match xs with
            // q X -(p)-> q0
            | [] -> if q' = q0 then [ PpdaRHS (p, []) ] else []
            // q X -(p)-> q0 X1 ... Xn
            | xs when lastHasQ' q' xs ->
                consVsTerm q0 q' xs
                |> List.map (fun lst -> PpdaRHS (p, lst))
            | _ -> []
        in
        Map.tryFind (q, x) ppda.ppdaRules
        |> Option.defaultValue []
        |> List.collect collector
    
    
    /// this is to build the variable, returns whether it is structurally zero
    and buildVar var =
        match HashMap.tryFind var cacheRes with
        | Some tmp -> tmp
        | None     ->
            HashMap.add var false cacheRes;
            let rhs = consRHS var in
            let res = List.isEmpty rhs in
            HashMap.add var res cacheRes;
            result <- (var, rhs) :: result;
            res
    
    let entryBuildVar () =
        initXDownQs
        |> List.map (fun q' ->
            PDVar (ppda.ppdaInitSt, ppda.ppdaBotX, q'))
        |> List.iter (ignore << buildVar)
    
    
    let arrangeResult result =
        let chooser q' =
            let var = PDVar (ppda.ppdaInitSt, ppda.ppdaBotX, q') in
            match HashMap.tryFind var cacheRes with
            | None -> IMPOSSIBLE ()
            | Some true -> None
            | Some false -> Some var
        in
        // x0 = \sum_q' <q(init) X(bot) q'>
        (EVX0, List.choose chooser initXDownQs
               |> List.map (fun var ->
                   PpdaRHS (NUMERIC_ONE, [ var ]))) ::
        // the rest of the equation system
        List.map (BiMap.fstMap EVNorm) result
    
    
    member x.GetEqSys () =
        let str =
            Map.toList dMap
            |> List.map (BiMap.sndMap Set.toList)
            |> List.map (fun (g, qs) ->
                let qs = List.map printQ qs in
                $"{printG g} |-> " + printSeq "[]" ", " qs)
            |> printSeq "" "\n  "
        in
        debugPrint $ "Down map generated:\n  " + str;
        if List.isEmpty result then ignore $ entryBuildVar ();
        arrangeResult result
    
    
    
let printPpdaEqSys lst =
    let mapper (PpdaRHS (p, vars)) =
        toString p + " * " + printSeq "[]" ", " vars
    in
    let mapper (var, lst) =
        toString var + " = " +
        "\n      " +
        printSeq "" "\n    + " (List.map mapper lst)
    in
    List.map mapper lst
    |> printSeq "" "\n"
    
    
/// to build the primitive pPDA equation system
let directBuildPrimitivePpdaEqSys ppda =
    debugPrint $ "pPDA to work: " + toString ppda;
    let obj = PpdaEqSysConsCtx ppda in
    let ret = obj.GetEqSys () in
    debugPrint $
        "Constructed Primitive pPDA Equation System:\n" +
        printPpdaEqSys ret;
    ret
    
    
let transVar ppda wrap (var : #IToRawVar<_,_>) =
    wrap $ var.ToRawVar ppda
    
    
let convertToEqSys_TP ppda lst =
    let transVar v = transVar ppda PVCProb v in
    let mapper lst =
        let mapper (PpdaRHS (c, lst)) =
            List.map transVar lst
            |> List.map FVar
            |> List.fold (*) (FConst c)
        in
        List.map mapper lst
        |> List.fold (+) (FConst NUMERIC_ZERO)
        |> optimiseFormula
    in
    List.map (BiMap.pairMap (transVar, mapper)) lst
    
    
let directPpdaEqSys_TP ppda =
    convertToEqSys_TP ppda $ directBuildPrimitivePpdaEqSys ppda
    
    
/// p * \prod_i P[Xi] + p * \sum_i E(Xi) * \prod_(j /= i) P[Xj]
/// The first `p` is because the step is fixed to be `1` -- just 1 time of reduction to be counted
/// The second `p` is the same as `hp` in the rPTSA case.
let private distAndSumItem ppda (PpdaRHS (p, lst)) =
    let p = FConst p in
    let toAllPVar lst =
        List.map (FVar << transVar ppda PVCProb) lst
    in
    let rec appAndDo pre post =
        match post with
        | curX :: post ->
            /// [ P[X1], ..., P[X(i-1)], P[X(i+1)], ..., P[Xn] ]
            let pVars = toAllPVar $ pre ++ post in
            /// E[Xi]
            let eVar = FVar $ transVar ppda PVCExp curX in
            /// p * E(Xi) * \prod_(j /= i) P[Xj]
            let thisRes = List.fold (*) p $ eVar :: pVars in
            thisRes + appAndDo (curX :: pre) post
        | [] ->
            List.fold (*) p $ toAllPVar pre  // p * \prod_i P[Xi]
    in
    appAndDo [] lst
    
    
let convertToEqSys_ETT ppda lst =
    let transVar wrap v = transVar ppda wrap v in
    let mapper lst =
        List.map (distAndSumItem ppda) lst
        |> List.fold (+) (FConst NUMERIC_ZERO)
        |> optimiseFormula
    in
    List.map (BiMap.pairMap (transVar PVCExp, mapper)) lst
    
    
let directPpdaEqSys_ETT ppda =
    let pes = directBuildPrimitivePpdaEqSys ppda in
    convertToEqSys_ETT ppda pes ++ convertToEqSys_TP ppda pes
    
    