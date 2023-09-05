module PTSV.Utils

open System
open System.Collections
open System.Collections.Generic
open System.IO
open System.Text.Json
open Microsoft.Z3
open PTSV.Global

let millisecondToSecond ms : double =
    (double ms) / 1e3

type ISettable<'v> =
    interface
        abstract member Set : 'v -> unit
    end
    
type IGettable<'v> =
    interface
        abstract member Get : unit -> 'v
    end
    
let set (obj : #ISettable<_>) v = obj.Set v
let get (obj : #IGettable<_>) = obj.Get ()

let initialiseProgram programPath =
    let p = new System.Diagnostics.Process ()
    p.StartInfo.FileName <- "/usr/bin/env"
    let commandList = [| "-S"; "bash"; "-c"; programPath |]
    for e in commandList do
        p.StartInfo.ArgumentList.Add e
    p.StartInfo.RedirectStandardInput <- true
    p.StartInfo.RedirectStandardOutput <- true
    p.StartInfo.CreateNoWindow <- true
    p.StartInfo.UseShellExecute <- false
    p.Start () |> ignore
    p

let ($) = (<|)
    
let inline flip f a b = f b a

/// give the program path, give back a function that input string and get back the answer
let runREDUCEInteractiveProgram
    programPath : string option -> string =
    let p = initialiseProgram programPath
    let write (s : string) = p.StandardInput.WriteLine s
    let rec readToBegin () =
        let mutable c = char (p.StandardOutput.Read ())
        let mutable ret = "" + string c
        if c > '9' || c < '0' then
            ret <- ret + readToBegin ()
        else
            while c <= '9' && c >= '0' do
                c <- char (p.StandardOutput.Read ())
                ret <- ret + string c
            if c = ':' then
                c <- char (p.StandardOutput.Read ())
                ret <- ret + string c
                if c <> ' ' then ret <- ret + readToBegin ()
                else ()
            else ret <- ret + readToBegin ()
        ret
    let beginString = readToBegin ()
    if Flags.PRINT_REDUCE_INFO then printfn $"{beginString}"
    let ret (os : string option) =
        match os with
        | None ->
            write "quit;"
            p.StandardInput.Flush ()
            p.StandardInput.Close ()
            let resString = p.StandardOutput.ReadToEnd ()
            p.WaitForExit ()
            resString
        | Some s ->
            write s
            readToBegin ()
    ret

/// simple modification so to continue working on Redlog for reals
let runRedlogInteractiveProgram
    programPath =
    let p = runREDUCEInteractiveProgram programPath
    p (Some "load_package redlog;") |> ignore
    p (Some "rlset reals;") |> ignore
    p

/// run a single time quantifier elimination
let runREDUCEQuantifierElimination
    programPath
    queryString : bool =
    let p = initialiseProgram programPath
    let write (s : string) = p.StandardInput.WriteLine s
    
    write "load_package redlog;"
    write "rlset reals;"
    write queryString
    write "quit;"
    p.StandardInput.Flush ()
    p.StandardInput.Close ()
    let resString = p.StandardOutput.ReadToEnd ()
    if Flags.PRINT_REDUCE_INFO = true then
        printfn $"{resString}"
    p.WaitForExit ()
    if resString.Contains "true" then true
    elif resString.Contains "false" then false
    else failwith "Invalid State"

let trimComments (str : string) =
    str.Split "\n"
    |> Array.map (fun x -> x.Split "//" |> Array.head)
    |> String.concat "\n"

/// input the path of the PReMo solver and also the inqury equation system *string*
/// convert to lines like:
/// 
/// x0 = x1 + x2
/// x1 = 0.5 + 0.3333333333 * x1
/// x2 = 0.1 * x1
/// 
/// Note that the function cannot accept division operator, hence all number should be converted to
/// floating point representation
let callPremoEquationEngine
        (premoPath : string)
        (eqSysStr: string)
        (additionalArgs : string list)
        =
    let proc = new System.Diagnostics.Process () in

    proc.StartInfo.FileName  <- "java";
    proc.StartInfo.Arguments <- $"""-jar {premoPath} --quiet {String.concat " " additionalArgs}""";

    proc.StartInfo.UseShellExecute        <- false;
    proc.StartInfo.RedirectStandardInput  <- true;
    proc.StartInfo.RedirectStandardOutput <- true;
    proc.StartInfo.RedirectStandardError  <- true;
    proc.StartInfo.CreateNoWindow         <- true;

    proc.Start () |> ignore;

    proc.StandardInput.WriteLine eqSysStr;
    proc.StandardInput.Close ();

    proc.WaitForExit ();
    
    if proc.ExitCode <> 0 then
        let error = proc.StandardError in
        let errorString = error.ReadToEnd () in
        Error $"Error encountered during PReMo execution: {errorString}"
    else
        let output = proc.StandardOutput in
        let rec readLines acc =
            if output.EndOfStream then List.rev acc
            else readLines $ output.ReadLine () :: acc in
        Ok $ readLines []

    
let toString x = $"{x}"

let generalBisectionApproximation criteria min max isLe =
    let mutable floor = min
    let mutable ceiling = max
    while criteria ceiling floor do
        let numToTest = (ceiling - floor) / (NumericType 2) + floor
        if isLe numToTest then
            ceiling <- numToTest
        else
            floor <- numToTest
    (floor, ceiling)
    

/// performs bisection from the given bound min and max
/// returns a pair (lower, upper) with upper - lower <= accuracy
let bisectionApproximation min max accuracy isLe =
    generalBisectionApproximation
        (fun ceiling floor -> ceiling - floor > accuracy)
        min
        max
        isLe

let genNewZ3Context () =
    let settings = Dictionary<string, string> ()
    let ctx =
//        match Flags.CORE_TIME_OUT with
//        | Some t ->
//            let elapsed = Flags.GLOBAL_TIMING.getTotalRawTime () in
//            if t <= elapsed then
//                raise (TimeoutException "Time out.")
//            // can only use the left time.
//            settings.Add("timeout", $"10")
//        | None -> ()
        new Context(settings)
    in
    let solver = ctx.MkSolver Const.NLSAT_ENABLE_STRING in
//    match Flags.CORE_TIME_OUT with
//    | Some t ->
//        let elapsed = Flags.GLOBAL_TIMING.getTotalRawTime () in
//        if t <= elapsed then
//            raise (TimeoutException "Time out.")
//        // can only use the left time.
//        let para = ctx.MkParams () in
//        let para = para.Add("timeout", 10u) in
//        solver.Parameters <- para
//    | None -> ()
    ctx, solver

let println x = printfn $"{x}"

let printFullSeq_full print hd tl sep seq =
    Seq.map print seq
    |> Seq.fold (fun r x -> if r = "" then x else r + sep + x) ""
    |> fun x -> hd + x + tl
    
let printFullSeq seq = printFullSeq_full (fun x -> $"{x}") "[" "]" ", " seq
    
let debugSameLinePrint (str : string) : unit =
    if Flags.DEBUG || Flags.INNER_DEBUG then printf $"{str}"
    
let debugPrint (str : string) : unit =
    if Flags.DEBUG || Flags.INNER_DEBUG then println str
    
let innerDebugPrint (str : string) : unit =
    if Flags.INNER_DEBUG then println str
    
let innerDebugSameLinePrint (str : string) : unit =
    if Flags.INNER_DEBUG then printf $"{str}"
    
let eqSysPrint extraGuafd eqSysStr : unit =
    if extraGuafd && not Flags.NOT_PRINT_EQ_SYS then println eqSysStr
    
let errPrint (str : string) : unit =
    eprintfn $"{str}"
    
let processPrint (str : string) : unit =
    if not Flags.SILENT_MODE then printfn $"{str}"
    
let printSeq (wrapper : string) splitter seq =
    let hd = wrapper.Substring(0, wrapper.Length / 2) in
    let tl = wrapper.Substring(wrapper.Length / 2) in
    printFullSeq_full toString hd tl splitter seq
    
let resultPrint (res : FinalResult) : unit =
    if Flags.DEBUG || Flags.INNER_DEBUG then println res;
    Flags.RESULT_ACC <- res :: Flags.RESULT_ACC

let turnZ3SolverResultIntoBool (solver : Solver) (query : BoolExpr []) =
    // copy the solver, otherwise, the outside solver will be affected
    let newSolver = solver.Context.MkSolver Const.NLSAT_ENABLE_STRING in
    let query = Array.append query solver.Assertions in
    let solver = newSolver in
    // assert the new query here
    solver.Assert query
    // set timeout
    match Flags.CORE_TIME_OUT with
    | Some t -> let elapsed = Flags.GLOBAL_TIMING.getTotalRawTime () in
                if t <= elapsed then failwith "Time out.";
                solver.Set("timeout", uint (t - elapsed).TotalMilliseconds)
    | None   -> ()
    innerDebugPrint $
            $"""Obtained Assertions to Solve: {Array.map toString solver.Assertions |> String.concat "\n"}""" +
            $"""New Assertions: {Array.map toString query |> String.concat "\n"}""";
    match solver.Check [] with
    | Status.SATISFIABLE -> true
    | Status.UNSATISFIABLE -> false
    | Status.UNKNOWN ->
        failwith $"NLSat could not determine the satisfiability of the query, reason: {solver.ReasonUnknown}"
    | _ ->
        failwith "Invalid Status"
        
let checkTimeOut msg =
    match Flags.CORE_TIME_OUT with
    | Some timeOut ->
        if Flags.GLOBAL_TIMING.getTotalRawTime () > timeOut then
            raise (TimeoutException $"{msg}")
    | None -> ()

type FindSet<'a when 'a : comparison> = {
    representative : 'a  // the element to represent this set
    pointerSet : Set<'a>
}

let unionFindSets fs1 fs2 =
    let newRepresentative = min fs1.representative fs2.representative
    let newPointerSet = Set.union fs1.pointerSet fs2.pointerSet
    { representative = newRepresentative
      pointerSet = newPointerSet }
    
type FindSetManager<'a when 'a : comparison> () =
    let mutable size = 0
    let mutable table : Map<'a, FindSet<'a>> = Map.empty
    let addNew k =
        // this check is not needed for the current definitions --
        // for only findOrAdd can call this private function
//        match Map.tryFind k table with
//        | None -> ()
//        | Some _ -> failwith "This is not valid add-new."
        let fs = { representative = k; pointerSet = Set.add k Set.empty }
        size <- size + 1
        table <- Map.add k fs table
        fs
    let update k v =
        // bugfix : should update all k to keep all k point to the same place
        Array.iter
            (fun k -> table <- Map.add k v table)
            (Set.toArray (Map.find k table).pointerSet)
    let findOrAdd o =
        match Map.tryFind o table with
        | Some fs -> fs
        | None -> addNew o
    member x.newEqRelationDeclare o1 o2 =
        let fs1 = findOrAdd o1
        let fs2 = findOrAdd o2
        if fs1 <> fs2 then
            let ufs = unionFindSets fs1 fs2
            update o1 ufs
            update o2 ufs
    member x.getSize () = size
    member x.isEmpty () = (size = 0)
    member x.tryFindRepresentative o =
        match Map.tryFind o table with
        | None -> None
        | Some o -> Some o.representative
    member x.getRawMap () = table

type IndexingTable<'a when 'a : comparison> =
    val mutable private table : Map<'a, int>
    val mutable private nextIndex : int
    
    new () = {
        table = Map.empty
        nextIndex = 0
    }
    new (initKey : 'a) = {
        table = Map.add initKey 0 Map.empty
        nextIndex = 1
    }
    
    static member CreateIndexingTableWithInitIndex initIndex =
        let ret = IndexingTable ()
        ret.nextIndex <- initIndex
        ret
    
    member x.lookUp e =
        match x.table.TryFind e with
        | Some i -> i
        | None ->
            x.table <- Map.add e x.nextIndex x.table
            x.nextIndex <- x.nextIndex + 1
            x.nextIndex - 1
    
    member x.addKey e = x.lookUp e |> ignore
    
    member x.swapIndex a b =
        x.table <-
            Map.map
                (fun _ v ->
                    if v = b then a
                    elif v = a then b
                    else v)
                x.table
    
    member x.refreshIndexWith id =
        let ret = Map.find id x.table
        x.swapIndex ret 0
        ret
    
    member x.printTableContent numberWrapper =
        Array.fold
            (fun rs (s, n) -> rs + numberWrapper n + " : " + $"{s}" + "\n")
            ""
            (Array.sortBy snd (Map.toArray x.table))
    
    member x.clear () =
        x.table <- Map.empty
        x.nextIndex <- 0
    /// if this indeed creates a new index, returns (Some newIndex), if there is already an index, returns None 
    member x.createNewIndex ne =
        match Map.tryFind ne x.table with
        | None ->
            x.table <- Map.add ne x.nextIndex x.table
            x.nextIndex <- x.nextIndex + 1
            x.nextIndex - 1
        | Some _ -> failwith "This index already existed."
    /// this contradicts the previous function, it only looks for index already exists
    member x.lookUpExistingIndex oe = Map.tryFind oe x.table
    member x.toArray () = fst (Array.unzip (Array.sortBy snd (Map.toArray x.table)))
    member x.getNextIndex () = x.nextIndex
    member x.getRawMap () = x.table
    
module IndexingTable = begin
    let lookup (x : IndexingTable<_>) = x.lookUp
end

let undefined _ = raise (Exception "Unimplemented Exception")

exception BreakMark

let isNullSeq cont = Seq.isEmpty cont

/// a shifted general fold function
let foldWith lst init func =
    let mutable ret = init in begin
    for e in lst do ret <- func e ret done; 
    ret end
    
let zip = Seq.zip

let uncurry f (a, b) = f a b
    
//let foldHashtable (tab : Hashtable) init (func : 'k * 'v -> 'r -> 'r) =
//    let mutable ret = init in begin
//    for e in tab do
//        let key = (e :?> DictionaryEntry).Key :?> 'k in
//        let v = (e :?> DictionaryEntry).Value :?> 'v in
//        ret <- func (key, v) init
//    done;
//    ret end
    
let IMPOSSIBLE msg = failwith $"IMPOSSIBLE: {msg}"

let (++) = List.append

let (>>=) option f =
    match option with
    | Some v -> f v
    | None -> None

let length lst = foldWith lst 0 $ fun _ x -> x + 1

let seqToHashtable seq =
    let tab = Hashtable () in
    for p in seq do tab.Add p done; 
    tab

let seqToHashSet seq =
    let set = HashSet () in
    for e in seq do set.Add e |> ignore done;
    set

let forEach lst func =
    foldWith lst () $ fun a () -> func a 

type HashTableEnumerator<'k, 'v>(data : IEnumerator) =
    interface IEnumerator<'k * 'v> with
        member this.Current =
            let entry = data.Current :?> DictionaryEntry in
            (entry.Key :?> 'k, entry.Value :?> 'v)
        member this.MoveNext() = data.MoveNext ()
        member this.Reset() = data.Reset ()
        member this.Current = data.Current
        member this.Dispose() = ()

/// a type-safe wrapper for Hashtable 
type HashMap<'k, 'v>(data : Hashtable) =
    class
        new () = new HashMap<'k, 'v>(Hashtable ())
        member x.size = data.Count
        member x.add (key : 'k) (value : 'v) = data[key] <- value
//            data.Add (key, value)
        member x.Item (key : 'k) = Option.get $ x.tryFind key
        member x.tryFind (key : 'k) =
            let v = data[key] in
            if v = null then None else Some (v :?> 'v)
        member x.remove (key : 'k) = data.Remove key
        member x.isEmpty () = data.Count = 0
        
        interface IEnumerable<'k * 'v> with
            member this.GetEnumerator(): IEnumerator<'k * 'v> =
                new HashTableEnumerator<'k, 'v>(data.GetEnumerator ())
            member this.GetEnumerator(): IEnumerator = data.GetEnumerator ()
    end
    
module HashMap = begin
    let tryFind k (map : HashMap<'k, 'v>) = map.tryFind k
    let fromSeq (s : seq<'k * 'v>) =
        let ret = new HashMap<'k, 'v> () in
        foldWith s () $ fun (k, v) () -> ret.add k v
        ret
    let fromMap map = fromSeq $ Map.toSeq map
    /// can re-map
    let add k v (map : HashMap<'k, 'v>) = map.add k v
    let union lst (map : HashMap<'k, 'v>) =
        foldWith lst () $ fun (k, v) () -> map.add k v 
    let size (map : HashMap<'k, 'v>) = map.size
    let containsKey k (map : HashMap<'k, 'v>) = match map.tryFind k with None -> false | Some _ -> true 
    let compute k f (map : HashMap<'k, 'v>) = match f $ map.tryFind k with
                                              | Some v -> map.add k v
                                              | None -> map.remove k
    let find k (map : HashMap<'k, 'v>) = Option.get $ map.tryFind k
    let isEmpty (map : HashMap<'k, 'v>) = map.isEmpty ()
    let filter pred (map : HashMap<'k, 'v>) =
        let nMap = Hashtable () in
        foldWith map () $ fun (k, v) () -> if pred k v then nMap.Add (k, v); 
        new HashMap<'k, 'v>(nMap)
    let map (f : 'a -> 'b) (map : HashMap<'k, 'a>) = let nMap = Hashtable () in
                                                     foldWith map () $ fun (k, v) () -> nMap.Add (k, f v);
                                                     new HashMap<'k, 'b>(nMap)
    let mapWithKey (f : 'k -> 'v -> 'v) (map : HashMap<'k, 'v>) = 
        let nMap = Hashtable () in
        forEach map $ fun (k, v) -> nMap.Add (k, f k v);
        new HashMap<'k, 'v>(nMap)
    let foldl f init (map : HashMap<'k, 'v>) = foldWith map init $ flip f
end

let (+++) = Seq.append

let readFileString (filePath : string) = 
    use sr = new StreamReader(filePath) in
    sr.ReadToEnd ()

let toList containers = foldWith containers [] $ fun e lst -> e :: lst 

let repeat t = Seq.initInfinite $ fun _ -> t

type ValueMark<'v>(v : 'v) =
    class
        inherit Exception "Just a value"
        member x.getValue () = v
    end

let getOne (lst : seq<'a>) =
    try
        for e in lst do raise $ ValueMark e done
        failwith "The sequence is empty."
    with
    | :? ValueMark<'a> as mark -> mark.getValue ()
    
let swap (a, b) = (b, a)

/// get the elements of a list except the last one 
let rec init lst =
    match lst with
    | [_] -> []
    | x :: xs -> x :: init xs
    | [] -> []

module BiMap = begin
    let fstMap f (a, b) = (f a, b)
    let sndMap f (a, b) = (a, f b)
    let pairMap (f1, f2) (a, b) = (f1 a, f2 b)
    let bothMap f (a, b) = (f a, f b)
end

/// xs `prefixOf` ys
let rec prefixOf xs ys =
    match xs, ys with
    | [], _ -> true
    | x :: xs, y :: ys -> x = y && prefixOf xs ys
    | _, [] -> false

let aggregate divFunc seq =
    Seq.groupBy (divFunc >> fst) seq
    |> Seq.map (BiMap.sndMap (Seq.map (divFunc >> snd)))

let aggregateList divFunc lst =
    List.groupBy (divFunc >> fst) lst
    |> List.map (BiMap.sndMap (List.map (divFunc >> snd)))

type NumericHelper<'n> =
    interface
        abstract getZero : unit -> 'n;
        abstract plus : 'n -> 'n -> 'n;
        abstract times : 'n -> 'n -> 'n;
        abstract minus : 'n -> 'n -> 'n;
        abstract divide : 'n -> 'n -> 'n;
    end

type NumericTypeHelper () =
    interface NumericHelper<NumericType> with
        member x.getZero () = NUMERIC_ZERO
        member this.divide var0 var1 = var0 / var1
        member this.minus var0 var1 = var0 - var1
        member this.plus var0 var1 = var0 + var1
        member this.times var0 var1 = var0 * var1
    end
    

/// Gaussian elimination to form an upper-right trapezium
/// returns the target matrix and the right vector along with the line and column label log
///
/// Example of possible results:
///    1 5 2 0 3 4
/// 1 [2 3 1 1 5 0 | 9]
/// 0 [0 4 1 1 0 0 | 3]
/// 2 [0 0 7 1 2 3 | 2]
/// 4 [0 0 0 0 0 0 | ?]
/// 3 [0 0 0 0 0 0 | ?]
/// where ? can be 0 or not, if they are zero, it means OK to have solution, otherwise, no solution
/// the matrix is not bound to be square
/// the first `int[]` means the log of lines (1 0 2 4 3)
/// and the second means the log of columns (1 5 2 0 3 4)
/// where the number means the original place in the input
///
/// TEST PASSED
let gaussianUpperRightTrapezium
    (copy : bool)
    (helper : #NumericHelper<'n>)
    (matrixA : 'n[][])
    (vecB : 'n[]) : 'n[][] * 'n[] * int[] * int[] =
    // initialise data and also check the validity of input
    (if Array.length matrixA <> Array.length vecB then
        failwith "Non-Valid Gaussian Input: line amount of A does not match that of B");
    let matrixA = if copy then Array.map Array.copy matrixA else matrixA in
    let vecB = if copy then Array.copy vecB else vecB in
    if Array.length matrixA = 0 then (matrixA, vecB, [||], [||]) else
    let lineLog = Array.indexed matrixA |> Array.map fst in
    let COLUMN_LENGTH = Array.length matrixA[0] in
    (if not $ Array.forall (fun lst -> Array.length lst = COLUMN_LENGTH) matrixA then
        failwith "Non-Valid Gaussian Input: A is not a strict matrix.");
    let columnLog = Array.init COLUMN_LENGTH id in
    if COLUMN_LENGTH = 0 then (matrixA, vecB, lineLog, columnLog) else
    let LINE_LENGTH = Array.length matrixA in
    
    // supportive definitions
    let swapLine l1 l2 =
        if l1 = l2 then () else
        let tmp = matrixA[l1] in
        matrixA[l1] <- matrixA[l2];
        matrixA[l2] <- tmp;
        let tmp = lineLog[l1] in
        lineLog[l1] <- lineLog[l2];
        lineLog[l2] <- tmp;
        let tmp = vecB[l1] in
        vecB[l1] <- vecB[l2];
        vecB[l2] <- tmp in
    let swapColumn c1 c2 =
        if c1 = c2 then () else
        let tmp = columnLog[c1] in
        columnLog[c1] <- columnLog[c2];
        columnLog[c2] <- tmp;
        flip Array.iter matrixA $ fun line ->
            let tmp = line[c1] in
            line[c1] <- line[c2];
            line[c2] <- tmp in
    
    let DIMENSION = min LINE_LENGTH COLUMN_LENGTH in
    // conduct computation
    for i in 0 .. DIMENSION - 1 do
        // make sure A[i][i] is not 0
        let getNext () =
            try
                for j in i .. LINE_LENGTH - 1 do
                    for k in i .. COLUMN_LENGTH - 1 do
                        if matrixA[j][k] <> helper.getZero () then begin
                            swapLine i j;
                            swapColumn i k;
                            raise BreakMark
                        end
                    done
                done;
                false
            with
            | BreakMark -> true
        in
        let updateFollowingLines () =
            for j in i + 1 .. LINE_LENGTH - 1 do
                let corr = helper.divide matrixA[j].[i] matrixA[i].[i] in
                matrixA[j][i] <- helper.getZero ();
                if corr <> helper.getZero () then begin
                    for k in i + 1 .. COLUMN_LENGTH - 1 do
                        matrixA[j][k] <- helper.minus matrixA[j].[k] (helper.times corr matrixA[i].[k])
                    done;
                    vecB[j] <- helper.minus vecB[j] (helper.times corr vecB[i])
                end
            done
        in
        
        if getNext () then updateFollowingLines ()
    done;
    (matrixA, vecB, lineLog, columnLog)
    
//type LinearEquationResult =
//    | NoSolution
//    | UniqueSolution of NumericType[]
//    | InfiniteSolutionsWithPositiveLFP of NumericType[]

let private gaussianUpperRightTrapeziumHasSolution
    (helper : #NumericHelper<_>) A B =
    Array.zip A B
    // only if the corresponding B place is 0 can the whole line of A be all 0
    // all zero to A and B is also acceptable
    |> Array.forall (fun (line, n) ->
        not (Array.forall (fun x -> x = helper.getZero ()) line) || n = helper.getZero ())
    
let private gaussianUpperRightTrapeziumFirstNonZeroIdx A =
    let LINE_LENGTH = Array.length A in
    let COL_LENGTH = Array.length $ Array.head A in
    let mutable idx = -1 in
    try
        for i = min LINE_LENGTH COL_LENGTH - 1 downto 0 do
            if A[i][i] <> NUMERIC_ZERO then begin
                idx <- i;
                raise BreakMark
            end
        done;
        idx
    with
    | BreakMark -> idx
    
    
/// this function will DESTROY the two input
/// we assume there is at least one element in A and B
let gaussianPositiveLFP matrixA vecB =
    let helper = NumericTypeHelper () in
    let A, B, _lineIds, colIds = gaussianUpperRightTrapezium false helper matrixA vecB in
    // check whether it has solution
    if not $ gaussianUpperRightTrapeziumHasSolution helper A B then None else
    // backward propagation
//    let LINE_LENGTH = Array.length lineIds in
    let COL_LENGTH = Array.length colIds in
    let ret = Array.init COL_LENGTH (fun _ -> NUMERIC_ZERO) in
    let firstNonZeroIdx = gaussianUpperRightTrapeziumFirstNonZeroIdx A in
    // if all 0, `i` will be `-1` so there will be no index
    for i = firstNonZeroIdx downto 0 do
        // ignore all possible latter indices, as they should all be 0 in LFP
        // update the return value according to B
        // the index of the variable is marked in colIds
        ret[colIds[i]] <- B[i] / A[i][i];
        // update all above lines
        for j = i - 1 downto 0 do
            // no need to update other parts, as they will be ignored
            B[j] <- B[j] - B[i] * A[j][i] / A[i][i]
        done
    done;
    Some ret

/// the default GFP value is `1`
let gaussianProbabilityGFP matrixA vecB =
    let helper = NumericTypeHelper () in
    let A, B, _lineIds, colIds = gaussianUpperRightTrapezium false helper matrixA vecB in
    // check whether it has solution
    if not $ gaussianUpperRightTrapeziumHasSolution helper A B then None else
    // backward propagation
    let COL_LENGTH = Array.length colIds in
    // default value is `1` now
    let ret = Array.init COL_LENGTH (fun _ -> NUMERIC_ONE) in
    let firstNonZeroIdx = gaussianUpperRightTrapeziumFirstNonZeroIdx A in
    // update the rest of the information information
    for i = firstNonZeroIdx downto 0 do
        B[i] <- B[i] - Array.fold (+) NUMERIC_ZERO A[i].[firstNonZeroIdx + 1..]
    done;
    for i = firstNonZeroIdx downto 0 do
        ret[colIds[i]] <- B[i] / A[i][i];
        // update all above lines
        for j = i - 1 downto 0 do
            // no need to update other parts, as they will be ignored
            B[j] <- B[j] - B[i] * A[j][i] / A[i][i]
        done
    done;
    Some ret

type MultiSet<'v> when 'v : comparison = Map<'v, int>
let toMultiSet seq : MultiSet<'v> =
    // sort is safe as to be multiset elements, the given type must be comparable
    Seq.sort seq
    |> Seq.fold (fun (prev, count, lst) e ->
        match prev with
        | None -> (Some e, 1, [])
        | Some oe ->
            if oe = e then (Some e, count + 1, lst)
            else (Some e, 1, (oe, count) :: lst))
        (None, 0, [])
    |> fun (lastE, count, lst) ->
        match lastE with
        | None -> Map.empty  // this means the given Sequence is empty
        | Some e -> Map.ofList $ (e, count) :: lst

let dfsTraverseAllNodes getNext init =
    let nodes = HashSet () in
    let rec traverse node =
        if nodes.Add node then for nNode in getNext node do traverse nNode done
    in
    traverse init;
    nodes

//let tapGlobalTiming () = Flags.GLOBAL_TIMING.tapInSecond ()

let logTimingMark mark = Flags.GLOBAL_TIMING.mark mark

/// get the time since the last tap and update the time
let tapTimingMark mark = Flags.GLOBAL_TIMING.tapMark mark

/// get the time since the last tap without updating the time
let getTimingFromMark mark = Flags.GLOBAL_TIMING.getMark mark

let lstEachAndRest lst =
    List.indexed lst
    |> List.map (fun (idx, e) ->
        List.splitAt idx lst
        |> BiMap.sndMap List.tail
        |> uncurry List.append
        |> fun lst -> (e, lst))

type AssignOnce<'v> () =
    let mutable data : 'v option = None
    member x.Data
        with get () =
            match data with
            | Some v -> v
            | None   -> failwith "Trying to take out value from non-assigned AssignOnce."
        and  set v =
            match data with
            | Some _ -> failwith "Trying to set again for type AssignOnce."
            | None   -> data <- Some v
    override x.ToString () = $"Once({data})"

let rec listSafeZip l1 l2 =
    match l1, l2 with
    | h1 :: l1, h2 :: l2 -> (h1, h2) :: listSafeZip l1 l2
    | _                  -> []

let revMap map =
    Map.toSeq map
    |> Seq.map swap
    |> Map.ofSeq
    
let currying f a b = f (a, b)

/// the version of take that terminates safely if the given sequence is not long enough
let rec seqSafeTake n seq =
    if n <= 0 || Seq.isEmpty seq then []
    else Seq.head seq :: seqSafeTake (n - 1) (Seq.tail seq)

let printStrTableInLaTeX (table : string [][]) =
    let header =
        "\\begin{tabular}{" + String.concat "|" (Array.map (fun _ -> "c") table[0]) + "}" in
    let tail =
        "\\end{tabular}"
    let linesMap line = String.concat " & " line in
    let lines =
        Array.map linesMap table[1..]
        |> String.concat " \\\\\n\t"
    in
    let fieldsHeader = String.concat " & " table[0] in
    header + "\n\t" +
    fieldsHeader + " \\\\\n\t\\hline\\hline\n\t" +
    lines + "\n" +
    tail

/// input a JSON format string with an array of map for each field
///
/// for example:
/// [
///     { "a" : 1, "b" : 2 }
///     { "a" : 3, "c" : 4 }
/// ]
/// To a table as:
/// a | b | c
/// ---------
/// 1 | 2 |  
/// 3 |   | 4
let parseJsonTableToStringTable (jsonTable : string) =
    let table = JsonSerializer.Deserialize<Map<string, string> []> jsonTable in
    let fields =
        Array.map (Map.toList >> List.map fst) table
        |> List.concat
        |> List.distinct
        |> Array.ofList
    in
    let linesMap line =
        let dataMap fieldName =
            match Map.tryFind fieldName line with
            | Some data -> data
            | None      -> " "
        in
        Array.map dataMap fields
    in
    let lines = Array.map linesMap table in
    Array.append [| fields |] lines

    
let switchColumnInMatrix copy i1 i2 matrix =
    let table =
        if copy then Array.map Array.copy matrix else matrix
    in
    for l in 0..table.Length - 1 do
        let tmp = table[l][i1] in
        table[l][i1] <- table[l][i2]
        table[l][i2] <- tmp
    done;
    matrix

let rearrangeMatrixColumns newFields matrix =
    let oldFilds = Array.head matrix in
    if Array.length oldFilds <> Array.length newFields then
        failwith "Re-arrange error: the given new fields length does not match that of the old fields."
    let oldFieldIndices =
        Array.head matrix
        |> Array.indexed
        |> Array.map swap
        |> HashMap.fromSeq
    in
    flip Array.map matrix (fun line ->
        Array.indexed line
        |> Array.map (fun (cNum, _) ->
            let realCNum =
                match HashMap.tryFind newFields[cNum] oldFieldIndices with
                | Some c -> c
                | None   ->
                    failwith
                        $"Re-arrange error: the given new field named \"{newFields[cNum]}\" does not exist."
            in
            line[realCNum]))
//    for cNum in 0..ret[0].Length - 1 do
//        let oriCNum =
//            match HashMap.tryFind newFields[cNum] oldFieldIndices with
//            | Some c -> c
//            | None   ->
//                failwith $"Re-arrange error: the given new field named \"{newFields[cNum]}\" does not exist."
//        in
//        for lNum in 0..ret.Length - 1 do
//            ret[lNum][cNum] <- matrix[lNum][oriCNum]
//        done
//    done;
//    ret

let guard b f = if b then f () else ()

/// a wrapper type to represent mutable value inside
type Cell<'t> () =
    let mutable content : 't option = None
    member x.HasValue with get () = Option.isSome content
    member x.Value
        with get () = Option.get content
        and  set value = content <- Some value
    interface ISettable<'t> with
        member this.Set var0 = this.Value <- var0
    end
    interface IGettable<'t> with
        member this.Get () = this.Value
    end
    override x.ToString () = toString content

type 't cell = Cell<'t>

let emptyCell () = Cell ()
/// make a cell and wrap the value to the cell
let toCell v = let ret = Cell () in ret.Value <- v; ret

module Cell = begin
    let get (cell : _ cell) = cell.Value
    let set value (cell : _ cell) = cell.Value <- value
    let hasValue (cell : _ cell) = cell.HasValue
    let optionGet (cell : _ cell) = if cell.HasValue then Some cell.Value else None
end

/// representing the intention of collecting values
/// every value can be collected (set) only once
/// for multiple-time set, use `Cell` instead
type Collect<'t> () =
    let mutable content : 't option = None
    member x.Collected () = Option.isSome content
    member x.Value
        with get () =
            match content with
            | Some c -> c
            | None   -> failwith "Variable Not Yet Collected."
        and  set info =
            match content with
            | Some _ -> failwith "Variable has already collected."
            | None   -> content <- Some info
    interface ISettable<'t> with
        member this.Set var0 = this.Value <- var0
    end
    interface IGettable<'t> with
        member this.Get () = this.Value
    end
    override x.ToString () = toString content

type 't collect = Collect<'t>

/// create a blank collect type as placeholder
/// a synonym of the default constructor `Collect ()`
let blank () = Collect ()
            
module Collect = begin
    let get (v : _ collect) = v.Value
    let set (c : _ collect) v = c.Value <- v
    let hasValue (c : _ collect) = c.Collected ()
    let hasCollected (c : _ collect) = c.Collected ()
    let collected (v : _ collect) = v.Collected ()
    let optionGet (c : _ collect) = if c.Collected () then Some c.Value else None
    /// create a blank collect type as placeholder
    /// a synonym of the default constructor `Collect ()`
    let blank () = Collect ()
    let collect v = let ret = blank () in ret.Value <- v; ret
end

let impGuard b v =
    if not b then IMPOSSIBLE ()
    else v

/// get the raw precision
/// 123 : 1.23e2  -> 2;
/// 0.01 : 1e-2   -> -2;
/// the `wrt` means the number to get with respect to
/// usual choices are 10 or 2
let getPrecision (wrt : NumericType) hint (num : NumericType) =
    let num = abs num in
    if num = NUMERIC_ZERO then 0 else
    let num = num * pown wrt (-hint) in
    let rec upFind precision num =
        if num >= NUMERIC_ONE then (precision, num)
        else upFind (precision - 1) (num * wrt) in
    let rec downFind precision num =
        if num < wrt then (precision, num)
        else downFind (precision + 1) (num / wrt) in
    downFind hint num
    |> uncurry upFind
    |> fst
    
    
/// do bisection by firstly expand to find the upper bound and then do usual bisection
/// The lower bound must be >= 0 and upper bound must > lower bound, hence upper bound must > 0
/// Returns the pair of (lowerBound, upperBound) with upperBound - lowerBound <= accuracy
let rec positiveOuterBisection accuracy isLe lower upper =
    if lower < NUMERIC_ZERO || upper < lower then
        failwith "Invalid initial bounds: lower bound < 0 or upper bound < lower bound.";
    if not $ isLe upper then positiveOuterBisection accuracy isLe upper (2 * upper)
    else bisectionApproximation lower upper accuracy isLe
    
    
let collectToMap lst =
    Map.ofList $ aggregateList id lst
    