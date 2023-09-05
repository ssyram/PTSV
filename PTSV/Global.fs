module PTSV.Global

open System
open System.Diagnostics
open System.Numerics
open System.Text
open Microsoft.FSharp.Reflection
open Rationals

[<Struct>]
[<CustomComparison>]
[<CustomEquality>]
type NumericType =
    val private r : Rational
    
    static member ZERO_TOLERANT : NumericType = NumericType (Rational (BigInteger 1, BigInteger 1e50))
    static member ZERO = NumericType Rational.Zero
    static member ONE = NumericType Rational.One
    static member private DOUBLE_ZERO_TOLERANT = double (NumericType.ZERO_TOLERANT.getR ())
    new (i : uint64) = NumericType (Rational (BigInteger i))
    new (i : int) = NumericType (Rational (BigInteger i))
    new (f : float) = NumericType (Rational.Approximate(f, NumericType.DOUBLE_ZERO_TOLERANT))
    new (nr : Rational) = { r = nr }
    member private x.getR () = x.r
    member x.getDouble () = double x.r
    static member Abs (x : NumericType) = NumericType (abs x.r)
    static member RoundUp (n : NumericType) =
        if (n.getR ()).Denominator.GetBitLength () > int64 64 then
            NumericType (Rational.Approximate (double (n.getR ()), NumericType.DOUBLE_ZERO_TOLERANT))
        else n
    static member Parse s =
        try
            NumericType (Rational.ParseDecimal s)
        with
        | _ -> NumericType (Rational.Parse s)
    // override this method to compare any number
    // for example, if the numeric inner-type is double, there should be tolerant range of comparison 
    override x.Equals obj =
        match obj with
        | :? NumericType as nt -> x.r.Equals (nt.getR ())
        | _ -> x.r.Equals obj
    override x.GetHashCode () = x.r.GetHashCode ()
    interface IEquatable<NumericType> with
        member x.Equals(other) = x.Equals other
    interface IFormattable with
        member x.ToString(format, formatProvider) = x.r.ToString(format, formatProvider)
    interface IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? NumericType as nt -> x.r.CompareTo (nt.getR ())
            | _ -> x.r.CompareTo obj
    static member get_Zero () = NumericType.ZERO
    static member get_One  () = NumericType.ONE
    static member Pow (n : NumericType, i : int) =
        NumericType (Rational.Pow (n.getR (), i))
    static member Pow (n : NumericType, i : NumericType) =
        NumericType (Rational.Pow (n.getR (), int (i.getR ())))
    static member ToInt (n : NumericType) =
        int (n.getR ())
    static member ToDouble (n : NumericType) =
        double (n.getR ())
    static member (+) (i : int, r : NumericType) =
        (NumericType i) + r
    static member (+) (r : NumericType, i : int) =
        r + (NumericType i)
    static member (-) (i : int, r : NumericType) =
        (NumericType i) - r
    static member (-) (r : NumericType, i : int) =
        r - (NumericType i)
    static member (*) (i : int, r : NumericType) =
        (NumericType i) * r
    static member (*) (r : NumericType, i : int) =
        r * (NumericType i)
    static member (/) (i : int, r : NumericType) =
        (NumericType i) / r
    static member (/) (r : NumericType, i : int) =
        r / (NumericType i)
    static member (+) (r1 : NumericType, r2 : NumericType) =
        NumericType (r1.getR () + r2.getR ()).CanonicalForm
    static member (*) (r1 : NumericType, r2 : NumericType) =
        NumericType (r1.getR () * r2.getR ()).CanonicalForm
    static member (-) (r1 : NumericType, r2 : NumericType) =
        NumericType (r1.getR () - r2.getR ()).CanonicalForm
    static member (/) (r1 : NumericType, r2 : NumericType) =
        if r2.getR () = Rational.Zero then
            failwith "Try dividing 0."
        NumericType (r1.getR () / r2.getR ()).CanonicalForm
    override x.ToString () = x.r.ToString ()
    member x.ToString (s : string) =
        match s.ToLower () with
        | "n30" ->
            $"{x.r} ({double x.r})"
        | "double" | "float" ->
            $"{double x.r}"
        | s when s.StartsWith "f" ->
            let targetLen =
                try Some (int (UInt16.Parse s[1..]))
                with | :? FormatException -> None
            in
            match targetLen with
            | None -> x.r.ToString s
            | Some targetLen ->
                if x.r < Rational.Zero then "-" + NumericType(-x.r).ToString s else
                let integer = x.r.WholePart in
                let fractional = x.r.FractionPart in
                let TEN = Rational (BigInteger 10) in
                let distanceToFirstDigit =
                    if fractional = Rational.Zero then 0 else
                    let rec findDist d n =
                        if n >= Rational.One then d - 1
                        else findDist (d + 1) (n * TEN)
                    in
                    findDist 1 (fractional * TEN)
                in
                let rawSeq =
                    Seq.append (Seq.init distanceToFirstDigit (fun _ -> '0')) fractional.Digits
                    |> Seq.truncate (targetLen + 1)
                    |> Array.ofSeq
                in
                let thisLen = Array.length rawSeq in
                if thisLen <= targetLen then
                    integer.ToString() + "." +
                    String(Array.append rawSeq (Array.init (targetLen - thisLen) (fun _ -> '0')))
                // round the number
                elif Array.last rawSeq <= '4' then
                    integer.ToString() + "." +
                    String(rawSeq[..rawSeq.Length-2])
                else
                    // the target number to print
                    let number =
                        rawSeq[..rawSeq.Length-2]
                        |> String
                        |> BigInteger.Parse
                        |> fun num ->
                            Rational(num + BigInteger.One, pown (BigInteger 10) targetLen) +
                            Rational(integer, BigInteger.One)
                    in
                    NumericType(number).ToString s
                    
        | _ -> x.r.ToString(s)

    member x.printInNlSatForm () =
        let r = x.r.CanonicalForm
        $"(/ {r.Numerator} {r.Denominator})"
        
    /// near equal
    static member (=~=) (r1 : NumericType, r2 : NumericType) =
        (abs (r1.getR () - r2.getR ())) < NumericType.ZERO_TOLERANT.getR ()

let NUMERIC_ZERO = NumericType.ZERO
let NUMERIC_ONE = NumericType Rational.One

module Const =
    let NLSAT_ENABLE_STRING = "QF_NRA"
    let NUMERIC_MARK_NUMBER = NUMERIC_ZERO - NUMERIC_ONE

let timeToSecond (time : TimeSpan) = time.TotalSeconds

/// Timing is just the wrapper of the global timing
type Timing () =
    let timing = Stopwatch ()
    let mutable previousTime = timing.Elapsed
    let mutable markMap = Map.empty
    do timing.Start () done
    
    member this.mark tag =
        markMap <- Map.add $"{tag}" timing.Elapsed markMap
    /// get the time since the last tap and update the time
    member this.tapMark tag =
        let now = timing.Elapsed in
        let prev = Map.find $"{tag}" markMap in
        markMap <- Map.add $"{tag}" now markMap
        now - prev
    /// get the time since the last tap without updating the time
    member this.getMark tag =
        let now = timing.Elapsed in
        let prev = Map.find $"{tag}" markMap in
        now - prev
    
    member this.tapInSecond () : double =
        let ret = (timing.Elapsed - previousTime)
        previousTime <- timing.Elapsed
        ret.TotalSeconds
    
    member this.totalTime () = timing.Elapsed
    member this.getTotalRawTime () = timing.Elapsed
    member this.reset () =
        previousTime <- TimeSpan.Zero
        markMap <- Map.empty
        timing.Restart ()
    
    
let splitCamelCases (str : string) =
    let rec compute revRes (prevBuilder : StringBuilder) idx =
        if idx >= str.Length then List.rev (prevBuilder.ToString() :: revRes)
        elif prevBuilder.Length = 0 then compute revRes (prevBuilder.Append str[idx]) (idx + 1)
        elif Char.IsUpper str[idx] then
            let lastChar = prevBuilder[prevBuilder.Length - 1] in
            if Char.IsUpper lastChar then compute revRes (prevBuilder.Append str[idx]) (idx + 1)
            else let newBuilder = StringBuilder () in
                 compute (prevBuilder.ToString () :: revRes) (newBuilder.Append str[idx]) (idx + 1)
        else  // the current one is lower or number
            let lastChar = prevBuilder[prevBuilder.Length - 1] in
            if Char.IsUpper lastChar then
                if prevBuilder.Length = 1 then compute revRes (prevBuilder.Append str[idx]) (idx + 1)
                else let newBuilder = (StringBuilder ()).Append lastChar in
                     compute
                         (prevBuilder.Remove(prevBuilder.Length - 1, 1).ToString () :: revRes)
                         (newBuilder.Append str[idx])
                         (idx + 1)
            else compute revRes (prevBuilder.Append str[idx]) (idx + 1)
    in
    Array.ofList (compute [] (StringBuilder ()) 0)
    

/// Any numeric printing should be controlled by this function to maintain consistency
/// except raw results from outside libraries
/// This can be changed
let mutable numericValuePrint : obj -> string = fun (obj : obj) ->
    match obj with
    | :? TimeSpan as time -> time.TotalSeconds.ToString "f4" + "s"
    | :? NumericType as num -> num.ToString "f4"
    | :? Double as d -> d.ToString "f4"
    | :? uint | :? uint64 | :? uint8 | :? uint16 as d -> String.filter Char.IsNumber (d.ToString ())
    | _ -> failwith $"Not Supported Numeric Format of Type: \"{obj.GetType().FullName}\""
    
    
/// all the results from the tool
type FinalResult =
    // the header
    | RHeader of string
    | RRealK of uint  // the true `k` from `check_K`
    | RReadFormat of string
    | RTotalTime of TimeSpan
    | RPahorsTranslationTime of TimeSpan
    | RPpdaTranslationTime of TimeSpan
    | RTpEqPrimitiveConsTime of TimeSpan
    | RTpEqSimpTime of TimeSpan
    | RTpEqPrimitiveScale of uint
    | RTpEqSimScale of uint
    | RTpEqTotalConsTime of TimeSpan
    | RTpASTTime of TimeSpan
    | RTpIsAST of Result<bool, string>  // either the result or the error message
    | RTpApproxValBisec of NumericType
    | RTpApproxValIter of NumericType
    | RTpApproxIterTimes of uint64
    | RTpApproxTimeBisec of TimeSpan
    | RTpApproxTimeIter of TimeSpan
    | RTpExploredVar of uint
    | REttEqPrimitiveConsTime of TimeSpan
    | REttEqSimpTime of TimeSpan
    | REttEqPrimitiveScale of uint
    | REttEqSimScale of uint
    | REttEqTotalConsTime of TimeSpan
    | REttQualTime of TimeSpan
    | REttHasVal of Result<bool, string>  // either the result or the error message
    | REttIsPAST of Result<bool, string>  // either the result or the error message
    | REttApproxValBisec of NumericType
    | REttApproxValIter of NumericType
    | REttApproxRawValBisec of NumericType
    | REttApproxRawValIter of NumericType
    | REttApproxIterTimes of uint64
    | REttApproxTimeBisec of TimeSpan
    | REttApproxTimeIter of TimeSpan
    | REttExploredVar of uint
    static member private FullNameConvert (str : string) =
        let getFullName (abbrName : string) =
            match abbrName.ToLower () with
            | "r" -> ""  // ignore the `R` prefix
            | "var" -> "variable"
            | "vars" -> "variables"
            | "tp" -> "termination probability"
            | "ett" -> "expected termination time"
            | "eq" -> "equation system"
            | "sys" -> ""  // it is declared above
            | "cons" -> "construction"
            | "time" -> "time"
            | "approx" -> "approximation"
            | "qual" -> "qualitative"
            | "val" -> "value"
            | "simp" -> "simplification"
            | "sim" -> "simplified"  // distinguish from the above
            | "bisec" -> "(bisection)"
            | "iter" -> "(iteration)"
            | "ast" -> "Almost Sure Termination (AST)"
            | "past" -> "Positive Almost Sure Termination (PAST)"
            | x -> x  // take the lower one
        in
        splitCamelCases str
        |> Array.map getFullName
        |> Array.filter (String.IsNullOrEmpty >> not)
        |> String.concat " "
    static member private FieldPrint (obj : obj) : string =
        match obj with
        | :? Result<bool, string> as res ->
            match res with
            | Ok b -> $"{b}"
            | Error msg -> msg.ToString().ToUpper()
        | :? string as str -> str
        | _ -> numericValuePrint obj
    member x.ToString(nameConvFunc, (fieldPrintFunc : obj -> string)) =
        FSharpValue.GetUnionFields(x, typeof<FinalResult>)
        |> fun (info, objs) ->
            let name = nameConvFunc info.Name
            match objs with
            | [||] -> $"{name}"
            | [| x |] -> $"{name}: {fieldPrintFunc x}"
            | arr ->
                let objStr =
                    Array.map fieldPrintFunc arr
                    |> String.concat ", "
                    |> fun x -> $"({x})"
                in
                $"{name}: {objStr}"
    override x.ToString () =
        x.ToString(FinalResult.FullNameConvert, FinalResult.FieldPrint)
    
    
module Flags =
    let mutable NO_QUALITATIVE_RESULT = false
    let mutable INNER_DEBUG = false
    let mutable DEBUG = false
    let mutable MAXIMUM_ALLOWED_VARIABLE_AMOUNT : uint64 = (uint64 1e7)
    let mutable ELIMINATE_INSTANT_PROJECTION = false
    let mutable USE_NEW = true
    let mutable SIMPLIFY = true
    let mutable DO_NOT_CHECK_PAST = false
    let mutable USER_SPECIFY_SIMPLIFY = false
    let mutable TEST_PRINT_RAW_SYSTEM = false
    let mutable PRINT_REDUCE_INFO = false
    let mutable ONLY_MODEL_CHECK = false
    let mutable MAX_ITER_ROUND : uint64 option = None
    let mutable NORMALISED_NEW_ALGORITHM = false
    let mutable KPTSA_NORMALISED = false
    let mutable APPROX_ACCURACY : NumericType = NumericType 1e-6
    let mutable APPROX_MIN_DIFF : NumericType = NumericType 1e-6
    let mutable EXPECTED_TERMINATION_TIME_ES_STANDARD_FORM = false
    let mutable TEST_PRINT_CONST_VAR = false
    let mutable COMPUTE_EXPECTED_TERMINATION_TIME_VALUE = false
    let mutable ALLOW_ITER_ROUND_UP = true
    let mutable PRINT_ITER_VALUES = false
    let mutable EXTERNAL_ETT_QUALITATIVE_CONFIRM = false
    let mutable COMPUTE_NON_AST_EXPECTED_TERMINATION_TIME = false
    let mutable CORE_TIME_OUT : TimeSpan option = None
    let mutable LINEAR_MAP_SYMBOL = "->"
    /// allow translation-style optimisation, like list increasing
    let mutable IS_TRANSLATED_KPTSA = false
//    let mutable DRA_MODEL_CHECKING = false
    let mutable PRELOAD_BINDINGS : Map<string, NumericType> = Map.empty
    /// directly cope with pPDA and pBPA, so that it is NOT converted to rPTSA
    /// but the equation system is generated directly
    let mutable DIRECT_PPDA = false
    let GLOBAL_TIMING = Timing ()
    /// This is a VERY BAD practice, as it requires information unknown at this point but to define below
    /// and it actually pre-requires State, LocalMemories and Gamma and DRA input alphabet to be `int`
    /// but as the components are already built, there is no other method to efficiently collect the information
    /// so this is defined here
    let mutable RPTSA_DRA_MAPPING : Map<int * int * int, int> option = None
    /// the first `int` is the id of non-terminal and the second `int` is the id of DRA input alphabet
    let mutable PAHORS_MAPPING_SOURCE : Map<int, int> option = None
    let mutable LOOK_AHEAD_NUM = 8
    
    // new flags
    let mutable TP_APPROXIMATION = true
    let mutable TP_QUALITATIVE = true
    let mutable TP_QUANTITATIVE_INQUIRY : (string * NumericType) option = None
    let mutable CHECK_PAST = true
    let mutable ETT_QUALITATIVE = true
    let mutable ETT_APPROXIMATION = true
    let mutable ETT_QUANTITATIVE_INQUIRY : (string * NumericType) option = None
    let mutable TP_APPROX_BY_BISECTION = true
    /// by default using iteration
    let mutable ETT_APPROX_BY_BISECTION = false
    let mutable ETT_REUSE_TP_RESULT = true
    let mutable DISPLAY_RATIONAL = false
    let mutable DISPLAY_FULL_TIME = false
    let mutable DISPLAY_POSITION = 4
    let mutable CHECK_K = false
    let mutable ENUM_STRING : int option = None
    let mutable KPTSA_Q_PRINT_TABLE : Map<int, string> = Map.empty
    let mutable KPTSA_M_PRINT_TABLE : Map<int, string> = Map.empty
    let mutable KPTSA_G_PRINT_TABLE : Map<int, string> = Map.empty
    let mutable BUILD_BFS = false
    let mutable NOT_PRINT_EQ_SYS = false
    let mutable REPORT_STUCK = false
    let mutable TP_RUN_BOTH_ITER_AND_BISEC = false
    let mutable ETT_RUN_BOTH_ITER_AND_BISEC = false
    let mutable PREMO_JAR_PATH : string = "./eqsolver.jar"
    let mutable PREMO_ADDITIONAL_ARGUMENTS : string list = [ "--maxSteps=0" ]
    let mutable ITER_BY_PREMO = false
    let mutable STACK_SIZE : int option = None
    /// The accumulation of the results -- reverse before printing
    let mutable RESULT_ACC : FinalResult list = []
    let mutable SILENT_MODE = false
    
module External =
    let mutable REDUCE_PATH = ""
    let mutable LD_LIBRARY_PATH = ""
