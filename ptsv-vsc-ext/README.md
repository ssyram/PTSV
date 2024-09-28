# ptsv README

The syntactic highlighting support for Probabilistic Tree-Stack Verifier (PTSV).
Refer to https://github.com/ssyram/PTSV for the full tool and input format description.

## Build Extension

To build the extension, install `vsce` first by:

> npm install -g vsce

Next, build by:

> vsce package

So that it generates a `.vsix` file, which is then utilsed by "install from VSIX" in VSCode.

The language `PTSV` is then supported in the language selection.
