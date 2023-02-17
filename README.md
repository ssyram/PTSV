# Probabilistic Tree-Stack Verifier (PTSV)
A tool for analysing termination probability and expected termination time of rPTSA and PAHORS.

## Build from Docker
The easiest way to run the project is running from Docker.
1. Install Docker (docs.docker.com/get-docker/) on local machine.
2. Change directory to the project directory.
3. Execute the command to create a docker image
> `docker build . -t ptsv`
4. Run the image built (with `docker run -it ptsv` or `docker run -dit ptsv`)
5. Run the following command to execute the tool
> `./PTSV filesToTest`
6. Or, run the `RunAll.sh` file to test all the examples in `paper examples`
> `./RunAll.sh`

## Build from `dotnet`
One may also run by compiling the codes by `dotnet`.
1. Install dotnet-sdk (https://dotnet.microsoft.com/en-us/download) (recommended version is 6.0.403)
2. Change directory to the root of this project (with this `README.md`)
3. Run the following command to build the project.
> `dotnet build`
4. Run the built `.dll` file.
   (usually in `./PTSV/bin/Debug/net6.0/`, so: `cd ./PTSV/bin/Debug/net6.0/` and then `dotnet PTSV.dll filesToTest`)
5. Or, run the whole project directly.
> `dotnet run --project PTSV filesToTest`

### Default Running Mode

> `./PTSV files`

Or

> `dotnet PTSV.dll files`

### Options

```
-d / -debug: printing various debugging information
-tp: to config what to analyse for termination probability
-ett: to config what to anlyse for expected termination time
-approx: to approximate the value
-qual: to compute qualitative results (AST / PAST)
-iter: to approximate the value by iteration
-bisec: to approximate the value by bisection (via Z3)
-min_diff NUMBER: specify iteration minimum difference as the iteration convergence criterion (by default 1e-6)
-accuracy NUMBER: specify bisection accuracy (by default 1e-6)
-max_iter_round NUMBER: specify maximum iteration rounds (by default infty)
-t <number>: setting time out, in milliseconds
[-D] NAME=NUMBER: to specify parse bindings (as additional `let` expressions)
-s: silent mode
-a: test all information
-no_expr: do not print the expressions and equation systems
-stack SIZE: specify the stack size to avoid the Stack Overflow problem
-enum_string [NUM]: to specify how many strings to enumerate when in converting to MCFG mode
-report_stuck: report the configurations that may involve yet will get stuck
-k / -check_k: check whether the declared `k` is correct (HIGH COST)
```

## File Format

A file consists of three parts:
1) (optional) some `let` value bindings;
2) a probabilistic model description.

### PAHORS

```
%BEGIN PAHORS type
<name> `:` <type>[.]
%END PAHORS type

%BEGIN PAHORS grammar
<name> <args list> [`(` <num expr> `)`] `:=` <term>.
%END PAHORS grammar
```

### rPTSA

#### General format

Config followed by the rPTSA rules definition,
where config is given by the following:

```
%BEGIN rPTSA config
restriction := <number>
q0 := <id>
m0 := <id>
gamma0 := <id>
%END rPTSA config

%BEGIN rPTSA rules
<rules>
%END rPTSA rules
```

There are two kinds of rules --
unrestricted branching or restricted branching.
The difference is on when should one place the probability expression.
In unrestricted branching, probabilities are placed for any one rule.
While in restricted one, probabilities can only appear in horizontal
transitions.

#### Unrestricted branching

```
(<q>, <m>, <gamma>, <prob expr>, <op>)[.]
```

where `<op>` is given by:

```
<q>
(<q>, <m>, down)
(<q>, <m>, up <gamma>)
\top
\Omega
```

where `\top` means termination, `\Omega` means divergence.
Note specially that to get `down` from `gamma0` is the same as `\top`.

#### Restricted Branching

```
(<q>, <m>, <gamma>, <op>)[.]
```

where `<op>` is given by
replacing the `<q>` in unrestricted branching operations with:

``` 
`<` {<q> : <prob expr>}+ `>`
```


### pPDA

The model of pPDA also consists of config and rules.
There are two kinds of possible input styles, the first is the explicit
style, which mimics the unrestricted rPTSA input,
the second is the rewriting rule style, which is the usual
style used in pPDA-related literatures.

``` 
%BEGIN pPDA config
q0 := <q>
gamma0 := <gamma>
%END pPDA config

%BEGIN pPDA rules
<rules>
%END pPDA rules
```

#### Explicit style

``` 
(<q>, <gamma>, <prob expr>, <op>)[.]
```

where `<op>` is one of the following:

``` 
<q>
pop
push <gamma>
```

#### Rewriting rule style

``` 
<q> <gamma> [`(` <prob expr> `)`] -> <q> <gamma>*.
```


### pBPA

For pBPA, there is only support for rewriting rules.

``` 
%BEGIN pBPA config
gamma0 := <gamma>.
%END pBPA config

%BEGIN pBPA rules
<gamma> [`(` <num expr> `)`] -> <gamma>*.
%END pBPA rules
```
