#! /usr/bin/env python

import sys
import re
import subprocess
import glob
import traceback

##errorpat = re.compile(r'\(\s*error\s+"[^"]*"\s*\)')
errorpat = re.compile(r'\(\s*error')
lp = re.compile(r'\(')
rp = re.compile(r'\)')

solvers = [
  "C:/cygwin/home/dcok/mybin/z3 -smt2",
  "C:/cygwin/home/dcok/mybin/z3-new -smt2",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental -m --strict-parsing",
  "C:/cygwin/home/dcok/mybin/cvc4-2015-06-30-win32-opt.exe --lang=smt2 --incremental -m --smtlib-strict",
  "C:/cygwin/home/dcok/apps/yices-2.3.1/yices-2.3.1/bin/yices-smt2.exe --interactive --incremental",
]
solversStdin = [
  "C:/cygwin/home/dcok/mybin/z3 -smt2 -in",
  "C:/cygwin/home/dcok/mybin/z3-new -smt2 -in",
  "C:/cygwin/home/dcok/mybin/cvc4-1.4-win32-opt.exe --lang=smt2 --incremental --interactive -m --strict-parsing",
  "C:/cygwin/home/dcok/mybin/cvc4-2015-06-30-win32-opt.exe --lang=smt2 --incremental --interactive -m --smtlib-strict",
  "C:/cygwin/home/dcok/apps/yices-2.3.1/yices-2.3.1/bin/yices-smt2.exe --interactive --incremental",
]

verbose = False

printSuccessIsNotDefault = False
errorOutputOnStderr = False
exitCommandDoesNotEmitSuccess = False
exitOnError = False
prompt = None

def dotest(solver,testfile, configure, usestdin):
  try:
    if verbose:
        print "-----"
    ok = True
    encounteredError = False
    newtestfile = testfile
    if printSuccessIsNotDefault and not configure:
        if verbose:
            print "-- Inserting (set-option :print-success true)"
        newtestfile = "tempin"
        tempfile = file(newtestfile,"w")
        tempfile.write("(set-option :print-success true) ; success\n");
        for line in file(testfile, "r"):
            tempfile.write( line )
        tempfile.flush()
        tempfile.close()
    outfile = file("out","w");
    if not configure and errorOutputOnStderr:
        errfile = outfile ## subprocess.STDOUT
        if verbose:
            print "Combining stderr and stdout"
    else:
        errfile = file("err","w")
    if usestdin:
        args = solver.split(" ")
        infile = file(newtestfile,"r")
        retcode = subprocess.call(args,stdin=infile,stdout=outfile,stderr=errfile)
        infile.close()
    else:
        solver = solver + " " + newtestfile
        args = solver.split(" ")
        retcode = subprocess.call(args,stdout=outfile,stderr=errfile)
    outfile.close()
    if not ( not configure and errorOutputOnStderr ) :
        errfile.close()
    infile = file(newtestfile,"r")
    number = 0
    parenlevel = 0
    for line in file("out","r"):
        line = line.rstrip('\r\n')
        number = number + 1
        if verbose:
            print "Actual: " + line
        if prompt:
            if not prompt in line:
            	continue
            a = line.split(prompt)
            line = a[len(a)-1]
            if len(line.strip()) == 0:
                continue
            if verbose:
                print "Actual stripped: " + line
            
        if parenlevel != 0:
            parenlevel = parenlevel + len(lp.findall(line)) - len(rp.findall(line))
            if verbose:
                print "Parenlevel " + str(parenlevel) + " " + line
            continue
        while True:
            inline = infile.readline()
            if len(inline) == 0:
                break
            inline = inline.strip()
            while len(inline) == 0 or inline[0] == ';':
                if verbose:
                    print "READ: " + inline
                inline = infile.readline()
                if len(inline) == 0:
                    break
                inline = inline.strip()
            if verbose:
                print "READ: " + inline
            info = inline.split(';')
            if len(info) > 1:
                if len(info[1].strip()) == 0:
                    continue
                break
        expected = info[1].strip()
        if verbose:
            print "Expected: " + expected
            
        if expected == line or (configure and expected in line):
            pass
            #print "line " + str(number) + " matches"
        elif "|" in expected:
            found = False
            for exp in expected.split("|"):
                if exp == line:
                    found = True
                    break
            if not found:
                ok = False
            if not found and not configure:
                if len(info) > 2:
                    print "[" + testfile + "] " + info[2].strip().replace("$actual",line).replace("$expected",expected)
                else:
                    print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line

        elif errorpat.match(line):
            if expected != "ERROR":
                ok = False
                if not configure:
                    if len(info) > 2:
                        print "[" + testfile +"] " + info[2].strip().replace("$actual",line).replace("$expected",expected)
                    else:
                        print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line
                
            encounteredError = True
            parenlevel = len(lp.findall(line)) - len(rp.findall(line))
            if parenlevel != 0:
                if verbose:
                    print "Parenlevel " + str(parenlevel) + " " + line
                continue
            
            #print "error line " + str(number) + " matches"
        elif not configure:
            if len(info) > 2:
                print "[" + testfile + "] " + info[2].strip().replace("$actual",line).replace("$expected",expected)
            else:
                print "mismatched output in line " + str(number) + ": " + expected + " vs. " + line
            ok = False
        else:
            ok = False

    if not (exitOnError and encounteredError):
        inline = infile.readline()
        while len(inline) != 0:
            inline = inline.strip()
            if len(inline) != 0 and inline[0] != ';':
                if not configure and exitCommandDoesNotEmitSuccess and "(exit)" in inline:
                    pass
                else:
                    if verbose:
                        print "Actual output aborted early: " + inline
                    ok = False
                    break
            inline = infile.readline()

    outfile.close()
    infile.close()
    return ok
  except:
    print "[" + testfile + "] EXCEPTION FAILURE"
#    traceback.print_exc()
    return False
    

def setModes(usestdin):
        global printSuccessIsNotDefault
        global errorOutputOnStderr
        global exitCommandDoesNotEmitSuccess
        global exitOnError
        global supportsProduceModels
        global supportsProduceProofs
        global supportsUnsatCores
        global supportsUnsatAssumptions
        global supportsProduceAssignments
        global supportsProduceAssertions
        global supportsGlobalDeclarations
        global supportsResourceLimit
        global supportsVerbosity
        global supportsRandomSeed
        global prompt
        exitOnError = False
        
        prompt = None
        if usestdin and "cvc4" in solver:
            prompt = "CVC4> "
            
        print ""
        print "Solver: " + solver 
        print "   use stdin: " + str(usestdin)
        printSuccessIsNotDefault = not dotest(solver, "default-print-success.mode.smt2", True, usestdin)
        exitCommandDoesNotEmitSuccess = not dotest(solver, "exit-emits-success.smt2", True, usestdin)
        exitOnError = dotest(solver, "config.continued-execution.smt2", True, usestdin)
        supportsProduceModels = dotest(solver, "config.produce-models.smt2", True, usestdin)
        supportsProduceProofs = dotest(solver, "config.produce-proofs.smt2", True, usestdin)
        supportsProduceUnsatCores = dotest(solver, "config.produce-unsat-cores.smt2", True, usestdin)
        supportsProduceUnsatAssumptions = dotest(solver, "config.produce-unsat-assumptions.smt2", True, usestdin)
        supportsProduceAssertions = dotest(solver, "config.produce-assertions.smt2", True, usestdin)
        supportsProduceAssignments = dotest(solver, "config.produce-assignments.smt2", True, usestdin)
        supportsGlobalDeclarations = dotest(solver, "config.global-declarations.smt2", True, usestdin)
        supportsResourceLimit = dotest(solver, "config.reproducible-resource-limit.smt2", True, usestdin)
        supportsRandomSeed = dotest(solver, "config.random-seed.smt2", True, usestdin)
        supportsVerbosity = dotest(solver, "config.verbosity.smt2", True, usestdin)
        

        ## FIXME - find a way to automatically detect these conditions:
        errorOutputOnStderr = "cvc4" in solver
        
        print "Modes: " + str(printSuccessIsNotDefault) + " " + str(errorOutputOnStderr) + " " + str(exitCommandDoesNotEmitSuccess) + " " + str(exitOnError)
        print "Capabilities:"
        print "  Prompt                                " + str(prompt)
        print "  Error behavior                        " + (":immediate-exit" if exitOnError else ":continued-execution")
        print "  Supports :produce-models              " + str(supportsProduceModels)
        print "  Supports :produce-proofs              " + str(supportsProduceProofs)
        print "  Supports :produce-assertions          " + str(supportsProduceAssertions)
        print "  Supports :produce-assignments         " + str(supportsProduceAssignments)
        print "  Supports :produce-unsat-cores         " + str(supportsProduceUnsatCores)
        print "  Supports :produce-unsat-assumptions   " + str(supportsProduceUnsatAssumptions)
        print "  Supports :global-declarations         " + str(supportsGlobalDeclarations)
        print "  Supports :reproducible-resource-limit " + str(supportsResourceLimit)
        print "  Supports :random-seed                 " + str(supportsRandomSeed)
        print "  Supports :verbosity                   " + str(supportsVerbosity)
        print "Non-standard configuration"
        any = False;
        if printSuccessIsNotDefault:
            print "  :print-success is false by default"
            any = True
        if errorOutputOnStderr:
            print "  error output is on stderr, instead of stdout"
            any = True
        if exitCommandDoesNotEmitSuccess:
            print "  (exit) command does not emit success response"
            any = True
        if not any:
            print " <<< none >>>"
        print ""

if __name__ == "__main__":
    count = 0
    failures = 0
    files = sys.argv[1:]
    if len(files) == 0:
        files = glob.glob('*.smt2')
    
    for solver in solvers:
        setModes(False)
        
        for f in files:
            if 'config' in f:
                continue
            count = count + 1
            if verbose:
                print ">>>>> " + f
            if not dotest(solver, f, False, False):
                ##print "TEST FAILED: " + f + " " + solver
                failures = failures + 1

    for solver in solversStdin:
        setModes(True)
        
        for f in files:
            if 'config' in f:
                continue
            count = count + 1
            if verbose:
                print ">>>>> " + f
            if not dotest(solver, f, False, True):
                ##print "TEST FAILED: " + f + " " + solver
                failures = failures + 1

    print str(failures) + " failures out of " + str(count) + " tests"
    sys.exit(0)    
