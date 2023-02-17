module PTSV.Output

open PTSV.Core
open PTSV.Global
open PTSV.NewEquationBuild
open Utils
open NewEquationBuild

type PrintTable =
    {
        stateTable : string[]
        memoryTable : string []
        gammaTable : string []
    }
type PrintType =
        | PTState of State
        | PTMemory of LocalMemory
        | PTGamma of Gamma

let lookUpPrintTable (table : PrintTable option) (toprint : PrintType) =
    match table with
    | Some t ->
        match toprint with
        | PTState q -> t.stateTable.[q]
        | PTMemory m -> t.memoryTable.[m]
        | PTGamma gamma -> t.gammaTable.[gamma]
    | None ->
        match toprint with
        | PTState q -> $"q_{{{q}}}"
        | PTMemory m -> $"m_{{{m}}}"
        | PTGamma gamma -> $"\\gamma_{{{gamma}}}"

let printInteractionList (l : InteractionList) table : string =
    if l = [] then
        "[]"
    else
        let mutable ret = ""
        for q, q' in l do
            let pq = lookUpPrintTable table (PTState q)
            let pq' = lookUpPrintTable table (PTState q')
            ret <- ret + $"({pq}, {pq'})"
        ret

let printU (U : Map<Gamma, InteractionList>) table : string =
    if Map.isEmpty U then "\\emptyset"
    else
        let mutable ret = "\\{"
        Map.iter
            (fun k v ->
            ret <- ret +
                $"{lookUpPrintTable table (PTGamma k)} \\mapsto "
                +
                printInteractionList v table
                + ", "
                )
            U
        ret <- ret + "\\}"
        ret

let printVariable (v : Variable) (table : PrintTable option) : string =
    let q, m, gamma, D, U, tp = v
    let pq = lookUpPrintTable table (PTState q)
    let pm = lookUpPrintTable table (PTMemory m)
    let pgamma = lookUpPrintTable table (PTGamma gamma)
    let pD = printInteractionList D table
    let pU = printU U table
    let stablePart = $"{{({pq}, {pm}, {pgamma}, {pD}, {pU}"
    match tp with
    | Varx -> $"x_{stablePart})}}"
    | VarDown qd ->
        let pqd = lookUpPrintTable table (PTState qd)
        $"Down_{stablePart}, {pqd})}}"
    | VarUp (gamma_u, qu) ->
        let pgu = lookUpPrintTable table (PTGamma gamma_u)
        let pqu = lookUpPrintTable table (PTState qu)
        $"Up_{stablePart}, ({pgu}, {pqu}))}}"

/// every time add happens, add new line in middle
/// every time multiply an add, which only appear in the second position, begin a new array
let rec printFormula (f : Formula) table : string =
    let mutable ret = ""
    match f with
    | FAdd (f1, f2) ->
        let pf1 = printFormula f1 table
        let pf2 = printFormula f2 table
        ret <- pf1 + " \\\\ \n +\\ & " + pf2
    | FMul (f1, FAdd (f2, f2')) ->
        let pf1 = printFormula f1 table
        let pf2 = printFormula (FAdd (f2, f2')) table
        ret <- pf1 + "\\cdot \\left(\\begin{array}{ll} \n & " + pf2 + "\n\\end{array}\\right)\n"
    | FMul (f1, f2) ->
        let pf1 = printFormula f1 table
        let pf2 = printFormula f2 table
        ret <- pf1 + " \\cdot " + pf2
    | FConst c -> ret <- $"{c}"
    | FVar v -> ret <- printVariable v table
    ret

let printExprVariable = Core.printExprVariable
let printExpr = Core.printExpr
let printExprSystem = Core.printExprSystem

/// print in a LaTeX form to display
let printFormulaSystem (vflist : (Variable * Formula) list) table : string =
    let mutable ret = ""
    let mutable count = 1
    for v, f in vflist do
        let pv = printVariable v table
        let pf = printFormula f table
        ret <- ret + " & " + pv + " = " + pf + "\\\\\\\\\n"
        count <- count + 1
        if count >= 1000 then failwith $"{ret}"
        if count % 4 = 0 then ret <- ret + "\\end{align*}\n\\begin{align*}"
    ret

/// a supporting function
/// Recover the definition string from an inner k-PTSA definition
let recoverStringDefinitionFromKPTSA (automata : KPTSA) : string =
    let mutable ret = $"Restriction := {automata.k}\n"
    ret <- ret + $"q0 := {printKPTSAState 0}\nm0 := {printKPTSALocMem 0}\ngamma0 := {printKPTSAGamma 0}\n\n"
    let outputEntry (q, m, gamma) v =
        List.iter
            (fun (p, op) ->
                let s = match op with
                        | TransDiv -> "Omega"
                        | TransDown (q', m') -> $"({printKPTSAState q'}, {printKPTSALocMem m'}, Down)"
                        | TransState q' -> $"{printKPTSAState q'}"
                        | TransTer -> "tt"
                        | TransUp (q', m', gamma') ->
                            $"({printKPTSAState q'}, {printKPTSALocMem m'}, Up {printKPTSAGamma gamma'})"
                ret <- ret + $"({printKPTSAState q}, {printKPTSALocMem m}, {printKPTSAGamma gamma}, {p}, {s})\n")
            v
    Map.iter
        outputEntry
        automata.delta
    ret

let genREDUCEQueryString
    (es : (int * Expr) list)
    (newQueryContent : string) : string =
    let mutable ret = "rlqe ex({"
    let iterVarList firstFunc secondFunc =
        let mutable first = true
        List.iter
            (fun (i, _) ->
                if first = true then
                    ret <- ret + firstFunc (printExprVariable i)
                    first <- false
                else ret <- ret + secondFunc (printExprVariable i))
            es
    // rlge ex({x0, x1, ..., xn}, 
    iterVarList id (fun x -> ", " + x)
    ret <- ret + "}, "
    // rlge ex({x0, x1, ..., xn}, 0 <= x0 <= 1 and ... 0 <= xn <= 1 and 
    iterVarList
        (fun x -> "0 <= " + x + " <= 1")
        (fun x -> " and 0 <= " + x + " <= 1")
    ret <- ret + " and "
    // x0 = f0(x) and x1 = f1(x) and ... xn = fn(x) and 
    List.iter
        (fun (i, e) ->
            ret <- ret + (printExprVariable i) + " = " + (printExpr e) + " and ")
        es
    ret <- ret + newQueryContent + ");"
    if Flags.DEBUG = true then
        printfn $"{ret}"
    ret

///// in order to support lisp print
///// for if d is an integer, the printed value will be integer and will not be recognised as Real sort
///// for example (+ a 1) will cause a sort conflicting in NLSAT query (a is of type Real)
///// it should be written as (+ a 1.0) to avoid the above issue
//let printProbability d =
//    if d = 1. then
//        "1.0"
//    elif d = 0. then
//        "0.0"
//    else
//        d.ToString("N30")

let lispPrintProbability = Core.lispPrintProbability

let rec lispPrintExpr = Core.lispPrintExpr

let genNLSatQueryString = Core.genNLSatQueryString
