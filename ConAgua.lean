-- con-agua: a Lean checker in x64 with an end-to-end proof. See PLAN.md.
module

public import ConAgua.L.Syntax
public import ConAgua.L.Semantics
public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.L.Examples
public import ConAgua.Compiler.Compile
public import ConAgua.Compiler.Run
public import ConAgua.Compiler.Tests
public import ConAgua.Compiler.WF
public import ConAgua.Compiler.Mem
public import ConAgua.Compiler.Step
public import ConAgua.Compiler.Rel
public import ConAgua.Compiler.SimExpr
public import ConAgua.Compiler.RunEq
public import ConAgua.Compiler.SimStmt
public import ConAgua.Compiler.SimCall
public import ConAgua.Compiler.SimFun
public import ConAgua.Compiler.SimStore
public import ConAgua.Compiler.Correct
public import ConAgua.Compiler.Main
public import ConAgua.Scan.Link
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Lit
public import ConAgua.Scan.LitLink
